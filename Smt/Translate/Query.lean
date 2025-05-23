/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Lean

import Smt.Data.Graph
import Smt.Translate.Commands
import Smt.Translate
import Smt.Tactic.EqnDef
import Smt.Util

namespace Smt.Translate.Query

open Lean Expr Meta
open Term

-- TODO: move all `Nat` hacks in this file to `Nat.lean`; see also issue #27

structure QueryBuilderM.Config where
  /-- Expressions to process. -/
  toProcess : List Expr := []
  /-- Expressions to define rather than just declare.
  Definition bodies are translated recursively. -/
  toDefine : List Expr := []

structure QueryBuilderM.State where
  graph : Graph Expr Unit := {}
  commands : Std.HashMap Expr Command := {}

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
  let (tm, depConsts, depFVars) ← Translator.translateExpr e
  let unknownConsts := depConsts.toArray.filterMap fun nm =>
    if Util.smtConsts.contains nm.toString then none else some (mkConst nm)
  if fvarDeps then
    let fvs := depFVars.toArray.map mkFVar
    return (tm, fvs ++ unknownConsts)
  else
    return (tm, unknownConsts)

/-- Return the body of a constant using its unfold equation theorem. Unlike raw delta-reduction,
this hides encoding tricks used to prove termination.

Given an equation theorem of the form `∀ x₁ ⬝⬝⬝ xₙ, c x₁ ⬝⬝⬝ xₙ = body`,
we return `fun x₁ ⬝⬝⬝ xₙ => body`. -/
def getConstBodyFromEqnTheorem (nm : Name) : MetaM Expr := do
  let some eqnThm ← getUnfoldEqnFor? (nonRec := true) nm
    | throwError "failed to retrieve equation theorem for '{nm}'"
  let eqnInfo ← getConstInfo eqnThm
  forallTelescopeReducing eqnInfo.type fun args eqn => do
    let some (_, _, e) := eqn.eq? | throwError "unexpected equation theorem{indentD eqn}"
    mkLambdaFVars args e

/-- Given the body `e` of a definition, make its application to `params` reducing *only* top-level
lambdas. For example, if `def foo (a : Int) : Int → Int := (+) a`, then `e = fun a => (+) a` and
supposing `params = #[a, b]`, we return `(+) a b`. -/
def makeFullyAppliedBody (e : Expr) (params : Array Expr) : MetaM Expr := do
  let numXs := countLams e
  let e ← instantiateLambda e (params.take numXs)
  mkAppOptM' e (params.toList.drop numXs |>.map some |>.toArray)
where
  countLams : Expr → Nat
    | lam _ _ t _ => 1 + countLams t
    | _ => 0

/-- Given a local (`let`) or global (`const`) definition, translate its body applied to `params`.
We expect `params` to contain enough free variables to make this a ground term. For example, given
`def foo (x : Int) : Int → Int := t`, we need `params = #[x, y]` and translate `t[x/x] y`.
Return the translated body, its dependencies, and whether the definition is recursive. -/
def translateDefinitionBody (params : Array Expr) : Expr → QueryBuilderM (Term × Array Expr × Bool)
  | e@(fvar id ..) => do
    let decl ← id.getDecl
    -- Look for an equational definition before defaulting to the let-body.
    let val ← getEqnDefLamFor? decl.userName
    let some val := val <|> decl.value?
      | throwError "trying to define {e} but it has no equational definition and is not a let-decl"
    let val ← makeFullyAppliedBody val params
    let (tmVal, deps) ← translateAndFindDeps val
    return (tmVal, deps, val.hasAnyFVar (· == id))
  | const nm .. => do
    let mutRecFuns := ConstantInfo.all (← getConstInfo nm)
    -- TODO: Replace by `DefinitionVal.isRec` check when (if?) it gets added to Lean core.
    if mutRecFuns.length > 1 then
      -- TODO: support mutually recursive functions.
      throwError "{nm} is a mutually recursive function, not yet supported"
    -- Look for an equational definition before defaulting to Lean's equational theorem.
    let val ← match (← getEqnDefLamFor? nm) with
    | some val => pure val
    | none => getConstBodyFromEqnTheorem nm
    let val ← makeFullyAppliedBody val params
    -- Note that we temporarily store `params` free variables as (incorrect) dependencies,
    -- but they are filtered out later in `addCommandFor`.
    let (tm, deps) ← translateAndFindDeps val
    return (tm, deps, Util.countConst val nm > 0)
  | e           => throwError "internal error, expected fvar or const but got{indentD e}\nof kind {e.ctorName}"

def addDefineCommandFor (nm : String) (e : Expr) (params : Array Expr) (cod : Expr)
    : QueryBuilderM (Array Expr) := do
  -- Translate the body and the parameter types.
  let (tmVal, deps, isRec) ← translateDefinitionBody params e
  let (tmParams, deps) ← params.foldrM (init := ([], deps)) fun param (tmParams, deps) => do
    let n := (← getFVarLocalDecl param).userName.toString
    let (tm, deps') ← translateAndFindDeps (← inferType param)
    return ((n, tm) :: tmParams, deps ++ deps')

  -- Is `e` a type?
  if cod.isSort && !cod.isProp then
    addCommand e <| .defineSort nm (tmParams.map (·.snd)) tmVal
    return deps
  else -- Otherwise it is a function or constant.
    let (tmCod, deps') ← translateAndFindDeps cod
    addCommand e <| .defineFun nm tmParams tmCod tmVal isRec
    return deps ++ deps'

def addDeclareCommandFor (nm : String) (e tp : Expr) (params : Array Expr) (cod : Expr)
    : QueryBuilderM (Array Expr) := do
  if cod.isSort && !cod.isProp then
    addCommand e <| .declareSort nm params.size
    return #[]
  else
    let (tmTp, deps) ← translateAndFindDeps tp
    addCommand e <| .declare nm tmTp
    return deps

/-- Build the command for `e : tp` and add it to the graph. Return the command's dependencies. -/
def addCommandFor (e tp : Expr) : QueryBuilderM (Array Expr) := do
  -- Is `tp` a `Prop` to assert?
  if (← Meta.inferType tp).isProp then
    let (tmTp, deps) ← translateAndFindDeps tp
    addCommand e <| .assert tmTp
    return deps

  trace[smt.translate.query] "{tp} : {← Meta.inferType tp}"

  -- Otherwise it is a local/global declaration with name `nm`.
  let nm ← match e with
    | fvar id .. =>
      match (← getThe TranslationM.State).uniqueFVarNames[id]? with
      | some nm => pure nm
      | none    => pure (← id.getUserName).toString
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
  deps.filterM (fun | fvar id .. => Option.isSome <$> id.findDecl? | _ => pure true)

/-- Build a graph of SMT-LIB commands to emit with dependencies between them as edges. -/
partial def buildDependencyGraph (g : Expr) : QueryBuilderM Unit := do
  go g
  for h in (← read).toProcess do
    go h
where
  go (e : Expr) : QueryBuilderM Unit := do
    if (← get).graph.contains e then
      return
    if !(e.isConst ∨ e.isFVar ∨ e.isMVar) then
      throwError "failed to build graph, unexpected expression{indentD e}\nof kind {e.ctorName}"

    let et ← inferType e
    let et ← instantiateMVars et
    trace[smt.translate.query] "processing {e} : {et}"

    -- HACK: `Nat` special cases
    if e matches const ``Nat .. then
      addCommand e Command.defNat
      return
    if e matches const ``Nat.sub .. then
      addCommand e Command.defNatSub
      go (mkConst ``Nat)
      addDependency e (mkConst ``Nat)
      return

    let deps ← addCommandFor e et

    trace[smt.translate.query] "deps: {deps}"
    for e' in deps do
      go e'
      addDependency e e'

end QueryBuilderM

def sortEndsWithNat : Term → Bool
  | .arrowT _ t    => sortEndsWithNat t
  | .symbolT "Nat" => true
  | _              => false

def natAssertBody (t : Term) : Term :=
  .mkApp2 (.symbolT ">=") t (.literalT "0")

/-- TODO: remove this hack once we have a tactic that replaces Nat goals with Int goals. -/
def natConstAssert (n : String) (args : List Name) : Term → MetaM Term
  | arrowT i@(symbolT "Nat") t => do
    let id ← mkFreshId
    return (forallT id.toString i
                   (imp id.toString (← natConstAssert n (id::args) t)))
  | arrowT a t => do
    let id ← mkFreshId
    return (forallT id.toString a (← natConstAssert n (id::args) t))
  | _ => pure $ natAssertBody (applyList n args)
  where
    imp n t := appT (appT (symbolT "=>") (natAssertBody (symbolT n))) t
    applyList n : List Name → Term
      | [] => symbolT n
      | t :: ts => appT (applyList n ts) (symbolT t.toString)

/-- TODO: Remove this function and its `Nat` those hacks. -/
def addCommand (cmd : Command) (cmds : List Command) : MetaM (List Command) := do
  let mut cmds := cmds
  cmds := cmd :: cmds
  match cmd with
  | .declare nm st =>
    if sortEndsWithNat st then
      let x ← natConstAssert nm [] st
      cmds := .assert x :: cmds
  | _ => pure ()
  return cmds

def emitVertex (cmds : Std.HashMap Expr Command) (e : Expr) : StateT (List Command) MetaM Unit := do
  trace[smt.translate.query] "emitting {e}"
  let some cmd := cmds[e]? | throwError "no command was computed for {e}"
  set (← addCommand cmd (← get))

def generateQuery (goal : Expr) (hs : List Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) :=
  withTraceNode `smt.translate.query (fun _ => pure .nil) do
    trace[smt.translate.query] "Goal: {← inferType goal}"
    trace[smt.translate.query] "Provided Hints: {hs}"
    let dfns ← hs.filterM fun h => do
      -- We need to define `const`s that are not theorems and `fvar`s from `let`s that are not assumptions.
      if h.isFVar then
        let fv := h.fvarId!
        let decl ← fv.getDecl
        (pure decl.isLet) <&&> notM (Meta.inferType decl.type >>= pure ∘ Expr.isProp)
      else if h.isConst then
        return !(Lean.wasOriginallyTheorem (← getEnv) h.constName)
      else
        return false
    trace[smt.translate.query] "Definitions: {dfns}"
    let ((_, st), _) ← QueryBuilderM.buildDependencyGraph goal
      |>.run { toProcess := hs, toDefine := dfns : QueryBuilderM.Config }
      |>.run { : QueryBuilderM.State }
      |>.run { uniqueFVarNames := fvNames : TranslationM.State }
    trace[smt.translate.query] "Dependency Graph: {st.graph}"
    -- The type of the proof generated by a solver depends on the order of asserions. We assert the
    -- Lean goal at the end of the query to simplify unification during proof reconstruction.
    let (_, cmds) ← StateT.run (st.graph.orderedDfs (hs ++ [goal]) (emitVertex st.commands)) []
    return cmds.reverse

end Smt.Translate.Query
