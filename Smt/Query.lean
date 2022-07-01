/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Lean
import Smt.Commands
import Smt.Graph
import Smt.Solver
import Smt.Translator
import Smt.Util

namespace Smt.Query

open Lean Expr Meta
open Solver Term

-- TODO: move all `Nat` hacks in this file to `Nat.lean`; see also issue #27

structure QueryBuilderM.State where
  graph : Graph Expr Unit := .empty
  commands : Std.HashMap Expr Command := .empty

abbrev QueryBuilderM := StateT QueryBuilderM.State TranslationM

namespace QueryBuilderM

def addCommand (e : Expr) (cmd : Command) : QueryBuilderM Unit :=
  modify fun st => { st with
    graph := st.graph.addVertex e
    commands := st.commands.insert e cmd
  }

def addDependency (e e' : Expr) : QueryBuilderM Unit :=
  modify fun st => { st with
    graph := st.graph.addEdge e e' ()
  }

/-- Translate an expression and compute its (non-builtin) dependencies. -/
def translateAndFindDeps (e : Expr) (fvarDeps := true) : QueryBuilderM (Term × Array Expr) := do
  let (tm, deps) ← Translator.translateExpr e
  let unknownConsts := deps.toArray.filterMap fun nm =>
    if Util.smtConsts.contains nm.toString then none else some (mkConst nm)
  if fvarDeps then
    let st : CollectFVars.State := {}
    let st := collectFVars st e
    let fvs := st.fvarIds.map mkFVar
    return (tm, fvs ++ unknownConsts)
  else
    return (tm, unknownConsts)

/-- Define a constant or function. The body `tmVal` is expected to be fully applied
to arguments matching the binder names in `tp`. -/
def buildDefineCommand (nm : Name) (tp : Expr) (isRec : Bool) (tmTp : Term) (tmVal : Term)
    : QueryBuilderM Command :=
  match tp with
  | forallE .. => do
    let (ps, tmCod) ← paramsAndCodomain tp
    return .defineFun nm.toString ps tmCod tmVal isRec
  | _ =>
    return .defineFun nm.toString [] tmTp tmVal isRec
where
  paramsAndCodomain (e : Expr) : QueryBuilderM (List (String × Term) × Term) := do
    match e with
    | forallE n t bd _ => do
      let (ps, cod) ← paramsAndCodomain bd
      return ((n.toString, ← Translator.translateExpr' t) :: ps, cod)
    | t => return ([], ← Translator.translateExpr' t)

-- TODO: support mutually recursive functions.
/-- Return the translated body, its dependencies, and whether it is recursive. -/
partial def translateConstBodyUsingEqnTheorem (nm : Name) : QueryBuilderM (Term × Array Expr × Bool) := do
  let mutRecFuns := ConstantInfo.all (← getConstInfo nm)
  -- TODO: Replace by `DefinitionVal.isRec` check when (if?) it gets added to Lean core.
  if mutRecFuns.length > 1 then
    throwError "{nm} is a mutually recursive function, not yet supported"
  let some eqnThm ← getUnfoldEqnFor? (nonRec := true) nm | throwError "failed to retrieve equation theorem for {nm}"
  let eqnInfo ← getConstInfo eqnThm
  let (tm, deps) ← body eqnInfo.type
  return (tm, deps, Util.countConst eqnInfo.type nm > 1)
where
  /-- Given an equation theorm of the form `∀ x₁ ⬝⬝⬝ xₙ, n x₁ ⬝⬝⬝ xₙ = body`,
      this function instantiates all occurrences of `x₁ ⬝⬝⬝ xₙ` in `body` and
      converts the resulting `Expr` into an equivalent SMT `Term`.  -/
  body (e :  Expr) : QueryBuilderM (Term × Array Expr) :=
    Meta.forallTelescopeReducing e fun _ tp => do
      let some (_, _, e) := tp.eq? | throwError "unexpected equation theorem{indentD e}"
      -- Note that we ignore free variable dependencies here because a constant's body
      -- can only depend on free variables introduced in this function.
      translateAndFindDeps (fvarDeps := false) e

-- Returns a list of additional dependencies
def addDefineCommand (nm : Name) (e : Expr) (tp : Expr) (tmTp : Term) : QueryBuilderM (Array Expr) := do
  match e with
  | fvar id .. =>
    let decl ← getLocalDecl id
    let some val := decl.value? | throwError "trying to define {nm} but it's not a let-declaration"
    -- Compute the let-binding body
    let (tmVal, deps) ← Meta.lambdaTelescope val fun args val =>
      translateAndFindDeps (val.instantiate args)
    -- Filter out fvars introduced by the lambda telescope. We cannot just ignore all fvars because
    -- the body might depend on other local bindings which we then have to translate.
    let deps ← deps.filterM (fun | fvar id .. => Option.isSome <$> findLocalDecl? id | _ => pure true)
    let cmd ← buildDefineCommand nm tp (val.hasAnyFVar (· == id)) tmTp tmVal
    addCommand e cmd
    return deps
  | const nm .. =>
    let (tmVal, deps, isRec) ← translateConstBodyUsingEqnTheorem nm
    let cmd ← buildDefineCommand nm tp isRec tmTp tmVal
    addCommand e cmd
    return deps
  | _          => throwError "internal error, expected fvar or const but got{indentD e}\nof kind {e.ctorName}"

/-- Build the command for `e` and add it to the graph. Return the command's dependencies. -/
def buildCommand (hs : List Expr) (e : Expr) (tp : Expr) (tmTp : Term) : QueryBuilderM (Array Expr) := do
  let sort l .. ← inferType tp | throwError "sort expected, got{indentD tp}"

  -- Is `tp` a `Prop` to assert?
  if l.toNat == some 0 then
    addCommand e <| .assert tmTp
    return #[]

  -- Otherwise `e` is a type or value to declare or define.

  let nm ← match e with
    | fvar id .. => pure (← getLocalDecl id).userName.toString
    | const n .. => pure n.toString
    | _          => throwError "internal error, expected fvar or const but got{indentD e}\nof kind {e.ctorName}"
  
  match tp with
    | sort .. =>
      addCommand e <| .declare nm tmTp
      return #[]
    | tp      =>
      if hs.elem e then
        addDefineCommand nm e tp tmTp
      else
        addCommand e <| .declare nm tmTp
        return #[]

/-- Build a graph of SMT-LIB commands to emit with dependencies between them as edges.
The input `hs` is a list of expressions to define rather than just declare. -/
partial def buildDependencyGraph (g : Expr) (hs : List Expr) : QueryBuilderM Unit := do
  go g
  for h in hs do
    go h
where
  go (e : Expr) : QueryBuilderM Unit := do
    if (← get).graph.contains e then
      return
    if !(e.isConst ∨ e.isFVar ∨ e.isMVar) then
      throwError "failed to build graph, unexpected expression{indentD e}\nof kind {e.ctorName}"

    let et ← inferType e
    let et ← instantiateMVars et
    trace[smt.debug.query] "processing {e} : {et}"

    -- HACK: `Nat` special cases
    if e matches const `Nat .. then
      addCommand e Command.defNat
      return
    if e matches const `Nat.sub .. then
      addCommand e Command.defNatSub
      go (mkConst `Nat)
      addDependency e (mkConst `Nat)
      return

    let (tmTp, deps) ← translateAndFindDeps et
    let deps' ← buildCommand hs e et tmTp

    let deps := deps ++ deps'
    trace[smt.debug.query] "deps: {deps}"
    for e' in deps do
      go e'
      addDependency e e'

end QueryBuilderM

def emitVertex (cmds : Std.HashMap Expr Command) (e : Expr) : StateT Solver MetaM Unit := do
  let mut solver ← get
  trace[smt.debug.query] "emitting {e}"
  let some cmd := cmds.find? e | throwError "no command was computed for {e}"
  solver ← cmd.emitCommand solver
  set solver

def generateQuery (goal : Expr) (hs : List Expr) (solver : Solver) : MetaM Solver :=
  traceCtx `smt.debug.generateQuery do
    trace[smt.debug.query] "Goal: {← inferType goal}"
    trace[smt.debug.query] "Provided Hints: {hs}"
    let ((_, st), _) ← QueryBuilderM.buildDependencyGraph goal hs |>.run {} |>.run {}
    trace[smt.debug.query] "Dependency Graph: {st.graph}"
    let (_, solver) ← StateT.run (st.graph.dfs $ emitVertex st.commands) solver
    return solver

end Smt.Query
