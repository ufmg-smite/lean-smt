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

structure QueryBuilderM.Config where
  /-- Expressions to define rather than just declare.
  Definition bodies are translated recursively. -/
  toDefine : List Expr := []

structure QueryBuilderM.State where
  graph : Graph Expr Unit := .empty
  commands : Std.HashMap Expr Command := .empty

abbrev QueryBuilderM := ReaderT QueryBuilderM.Config <| StateT QueryBuilderM.State TranslationM

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

/-- Translate an expression and compute its (non-SMT-builtin) dependencies.
When `fvarDeps = false`, we filter out dependencies on fvars. -/
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

-- TODO: support mutually recursive functions.
/-- Translate the body of a constant in the environment. See `translateDefinitionBody`. -/
partial def translateConstBodyUsingEqnTheorem (nm : Name) (params : Array Expr)
    : QueryBuilderM (Term × Array Expr × Bool) := do
  let mutRecFuns := ConstantInfo.all (← getConstInfo nm)
  -- TODO: Replace by `DefinitionVal.isRec` check when (if?) it gets added to Lean core.
  if mutRecFuns.length > 1 then
    throwError "{nm} is a mutually recursive function, not yet supported"
  
  /- Given an equation theorem of the form `∀ x₁ ⬝⬝⬝ xₙ, c x₁ ⬝⬝⬝ xₙ = body`, we first instantiate
     all occurrences of `x₁ ⬝⬝⬝ xₙ` in `body`. We must then instantiate with the remaining `params`
     in case the `body` is partly or entirely curried. We then convert the resulting `Expr` into
     an equivalent SMT `Term`. -/
  let some eqnThm ← getUnfoldEqnFor? (nonRec := true) nm | throwError "failed to retrieve equation theorem for {nm}"
  let eqnInfo ← getConstInfo eqnThm
  let numXs := countBinders eqnInfo.type
  let eqn ← instantiateForall eqnInfo.type (params.shrink numXs)
  let some (_, _, e) := eqn.eq? | throwError "unexpected equation theorem{indentD eqn}"
  let eBody ← mkAppOptM' e (params.toList.drop numXs |>.map some |>.toArray)
  -- Note that we ignore free variable dependencies here because a constant's body
  -- can only depend on free variables introduced as `params`.
  let (tm, deps) ← translateAndFindDeps eBody (fvarDeps := false)
  return (tm, deps, Util.countConst eqnInfo.type nm > 1)
where
  countBinders : Expr → Nat
    | forallE _ _ t _ => 1 + countBinders t
    | _ => 0

/-- Given a local (`let`) or global (`const`) definition, translate its body applied to `params`.
We expect `params` to contain enough free variables to make this a ground term. For example, given
`def foo (x : Int) : Int → Int := t`, we need `params = #[x, y]` and translate `t[x/x] y`.
Return the translated body, its dependencies, and whether the definition is recursive. -/
def translateDefinitionBody (params : Array Expr) : Expr → QueryBuilderM (Term × Array Expr × Bool)
  | e@(fvar id ..) => do
    let decl ← getLocalDecl id
    let some val := decl.value? | throwError "trying to define {e} but it's not a let-declaration"
    let numXs := countLams val
    let val ← instantiateLambda val (params.shrink numXs)
    let val ← mkAppOptM' val (params.toList.drop numXs |>.map some |>.toArray)
    let (tmVal, deps) ← translateAndFindDeps val
    return (tmVal, deps, val.hasAnyFVar (· == id))
  | const nm .. => translateConstBodyUsingEqnTheorem nm params
  | e           => throwError "internal error, expected fvar or const but got{indentD e}\nof kind {e.ctorName}"
where
  countLams : Expr → Nat
    | lam _ _ t _ => 1 + countLams t
    | _ => 0

/-- Assuming `e : Sort u` and `u` is constant, return `u`. Otherwise fail. -/
def getSortLevel (e : Expr) : QueryBuilderM Nat := do
  let sort l .. ← inferType e | throwError "sort expected, got{indentD e}"
  let some l := l.toNat | throwError "type{indentD e}\nhas varying universe level {l}"
  return l

def addDefineCommandFor (nm : String) (e : Expr) (params : Array Expr) (cod : Expr)
    : QueryBuilderM (Array Expr) := do
  -- Translate the body and the parameter types.
  let (tmVal, deps, isRec) ← translateDefinitionBody params e
  let (tmParams, deps) ← params.foldrM (init := ([], deps)) fun param (tmParams, deps) => do
    let n := (← getFVarLocalDecl param).userName.toString
    let (tm, deps') ← translateAndFindDeps (← inferType param)
    return ((n, tm) :: tmParams, deps ++ deps')

  -- Is `e` a type?
  if 1 < (← getSortLevel cod) then
    addCommand e <| .defineSort nm (tmParams.map (·.snd)) tmVal
    return deps
  else -- Otherwise it is a function or constant.
    let (tmCod, deps') ← translateAndFindDeps cod
    addCommand e <| .defineFun nm tmParams tmCod tmVal isRec
    return deps ++ deps'

def addDeclareCommandFor (nm : String) (e tp : Expr) (params : Array Expr) (cod : Expr)
    : QueryBuilderM (Array Expr) := do
  if 1 < (← getSortLevel cod) then
    addCommand e <| .declareSort nm params.size
    return #[]
  else
    let (tmTp, deps) ← translateAndFindDeps tp
    addCommand e <| .declare nm tmTp
    return deps

/-- Build the command for `e : tp` and add it to the graph. Return the command's dependencies. -/
def addCommandFor (e tp : Expr) : QueryBuilderM (Array Expr) := do
  -- Is `tp` a `Prop` to assert?
  if let 0 ← getSortLevel tp then
    let (tmTp, deps) ← translateAndFindDeps tp
    addCommand e <| .assert tmTp
    return deps

  trace[smt.debug.query] "{tp} : Sort {← getSortLevel tp}"

  -- Otherwise it is a local/global declaration with name `nm`.
  let nm ← match e with
    | fvar id .. => pure (← getLocalDecl id).userName.toString
    | const n .. => pure n.toString
    | _          => throwError "internal error, expected fvar or const but got{indentD e}\nof kind {e.ctorName}"

  -- Introduce the declaration's parameters and codomain.
  let deps ← Meta.forallTelescopeReducing tp fun params cod => do
    -- Should we define the body of `e`?
    if (← read).toDefine.elem e then addDefineCommandFor nm e params cod
    -- Otherwise we just declare it.
    else addDeclareCommandFor nm e tp params cod

  -- Filter out fvars introduced by the forall telescope. We cannot just ignore all fvars because
  -- the definition might depend on local bindings which we then have to translate.
  deps.filterM (fun | fvar id .. => Option.isSome <$> findLocalDecl? id | _ => pure true)

/-- Build a graph of SMT-LIB commands to emit with dependencies between them as edges. -/
partial def buildDependencyGraph (g : Expr) : QueryBuilderM Unit := do
  go g
  for h in (← read).toDefine do
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

    let deps ← addCommandFor e et

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
    let ((_, st), _) ← QueryBuilderM.buildDependencyGraph goal
      |>.run { toDefine := hs : QueryBuilderM.Config }
      |>.run { : QueryBuilderM.State }
      |>.run { : TranslationM.State }
    trace[smt.debug.query] "Dependency Graph: {st.graph}"
    let (_, solver) ← StateT.run (st.graph.dfs $ emitVertex st.commands) solver
    return solver

end Smt.Query
