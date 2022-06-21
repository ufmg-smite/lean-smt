/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Tactic

import Smt.Tactic

namespace Lean.Meta
open Elab Tactic

-- TODO(WN): Might want to expose the `Syntax`-less versions of `Tactic.Rewrite` stuff in core.

def rewriteTarget (e : Expr) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let r ← rewrite (← getMainGoal) (← getMainTarget) e symm (config := config)
    let mvarId' ← replaceTargetEq (← getMainGoal) r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (e : Expr) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let localDecl ← getLocalDecl fvarId
    let rwResult ← rewrite (← getMainGoal) localDecl.type e symm (config := config)
    let replaceResult ← replaceLocalDecl (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

/-- Try to rewrite using `pf : _ = _` everywhere except for local declarations matching `skipPred`. -/
def tryRewriteEverywhere (pf : Expr) (skipPred : LocalDecl → Bool) : TacticM Unit := do
  Tactic.withMainContext do
    try Meta.rewriteTarget pf false {}
    catch _ => pure ()
    let lctx ← getLCtx
    for localDecl in lctx do
      if skipPred localDecl then continue
      try Meta.rewriteLocalDecl pf false localDecl.fvarId {}
      catch _ => pure ()

end Lean.Meta

namespace Smt.Concretize

open Lean Elab Meta Tactic

/-- Some crap we need to store while processing the tactic. -/
structure ConcretizationData where
  eConcrete : Expr
  /-- `var.$nm : _` created by `generalize` -/
  fvVar : FVarId
  /-- `eqVar.$nm : $eConcrete = var.$nm` created by `generalize` -/
  fvEqVar : FVarId
  /-- `eqBody.$nm : var.$nm = $eBody`

  We use this equality to simulate a let-binding since it is not easy to rewrite
  in a let-binding body. Note that other concretization steps may recursively rewrite
  in `eBody`. -/
  fvEqBody : FVarId

def ConcretizationData.create (nm : Name) (eConcrete : Expr) : TacticM ConcretizationData := 
  liftMetaTacticAux fun mvarId => do
    let varName := `var ++ nm
    let eqVarName := `eqVar ++ nm
    let eqBodyName := `eqBody ++ nm

    let (#[fvVar, fvEqVar], mvarId) ← Meta.generalize mvarId #[{
        expr := eConcrete
        xName? := varName
        hName? := eqVarName
      }] | throwError "unexpected generalize fvars"

    -- `@f a b` ≡ `(fun x y z w => t) a b` ≡ `fun z w => t[a/x,b/y]`
    let eBody ← withTransparency TransparencyMode.all <| whnf eConcrete
    let tpEqBody ← mkEq eConcrete eBody
    let pfEqBody ← mkEqRefl eConcrete
    let (fvEqBody, mvarId) ← intro1P (← assert mvarId eqBodyName tpEqBody pfEqBody)

    let ret := { eConcrete, fvVar, fvEqVar, fvEqBody }
    return (ret, [mvarId])

def ConcretizationData.getBody (conc : ConcretizationData) : TacticM Expr :=
  withMainContext do
    let tp ← inferType (mkFVar conc.fvEqBody)
    let some (_, _, eBody) := tp.eq?
      | throwError "internal error, expected equality but got {tp}"
    return eBody

structure State where
  /-- Stores all concretizations and their equality hypotheses. These should not depend on a local
  context other than let-decls in the goal's. -/
  concretizations : Std.RBMap Name ConcretizationData Name.quickCmp
  /-- Cache of concretization names, lookupable by the concretization. -/
  cache : DiscrTree Name
  /-- In a single iteration of the algorithm, new concretizations found. -/
  newConcretizations : Std.RBMap Name Expr Name.quickCmp
  /-- In a single iteration of the algorithm, names of concretizations corresponding to all
  polymorphic terms found. These might or might not already have `generalize` hypotheses
  which we introduce lazily. Rewriting with each must make progress on concretizing the goal. -/
  foundConcretizables : NameSet

abbrev ConcretizeM := StateT State TacticM

def withMainContext (x : ConcretizeM α) : ConcretizeM α := do
  controlAt TacticM fun mapInBase => Tactic.withMainContext (mapInBase x)

def traceLCtx : MetaM Unit := traceCtx `smt.debug.lctx do
  for localDecl in (← getLCtx) do
    trace[smt.debug.concretize.lctx] "{localDecl.userName} : {localDecl.type} {if localDecl.isAuxDecl then "(aux)" else ""})"

def getCached? (e : Expr) : ConcretizeM (Option Name) := do
  -- We use `withExtra` as concretizations can be prefixes of the full application.
  let nms ← (←get).cache.getMatchWithExtra e
  if nms.size > 1 then unreachable!
  if let #[(nm, _)] := nms then
    trace[smt.debug.concretize.cache] "hit {e} ↦ {nm}"
    return some nm
  trace[smt.debug.concretize.cache] "miss {e}"
  return none

def addNewConcretization (nm : Name) (e : Expr) : ConcretizeM Unit := do
  let st ← get
  let cache ← st.cache.insert e nm
  let newConcretizations := st.newConcretizations.insert nm e
  set { st with cache, newConcretizations }

def foundConcretizable (nm : Name) : ConcretizeM Unit :=
  modify fun st => { st with foundConcretizables := st.foundConcretizables.insert nm }

def concretizeApp (e : Expr) : ConcretizeM TransformStep := do
  if !e.isApp then return .visit e
  e.withApp fun fn args => do
    let .const declName .. := fn | return .visit e
    -- NB: we end up visiting the Eq type argument here which isn't ideal
    if `Eq == declName then return .visit e
    -- HACK: don't traverse typeclass projections. We should have a list of which ones
    -- to skip though.
    if let some { fromClass := true, .. } ← getProjectionFnInfo? declName then
      return .done e
    -- HACK: don't traverse types
    if (← inferType e).isType then
      return .done e

    -- Hits if an application with the same concretization was seen before.
    if let some nm ← getCached? e then
      foundConcretizable nm
      return .done e

    let info ← getFunInfoNArgs fn args.size
    let mut concreteArgs := #[]
    for (pi, a) in info.paramInfo.zip args do
      let argTp ← inferType a
      let isConcretizable :=
        !a.hasLooseBVars ∧ !a.hasFVar ∧ (argTp.isType ∨ pi.hasFwdDeps ∨ pi.isInstImplicit)
      if isConcretizable then concreteArgs := concreteArgs.push (some a)
      else break
    if concreteArgs.isEmpty then return .visit e

    let eConcrete ← mkAppOptM' fn concreteArgs
    trace[smt.debug.concretize.app] "{e} ==> {eConcrete}"

    -- Add a suffix for every concretised argument.
    let nm ← concreteArgs.foldlM (init := declName) fun nm arg? => do
      if let some arg := arg? then
        let txt := toString (← ppExpr arg)
        let txt := txt.replace " " "_"
        return nm ++ Name.mkSimple txt
      else return nm
    let nm ← mkFreshUserName nm

    addNewConcretization nm eConcrete
    foundConcretizable nm

    -- Even though they may have concretizable subterms, we do not visit children
    -- as they will be taken care of in the next iteration.
    return .done e

partial def loop : ConcretizeM Unit := traceCtx `smt.debug.concretize.loop do
  modify fun st => { st with
    newConcretizations := Std.RBMap.empty
    foundConcretizables := NameSet.empty
  }

  let goal ← getMainTarget
  let _ ← withMainContext <| Meta.transform goal (m := ConcretizeM) (pre := concretizeApp)

  for (nm, eConcrete) in (← get).newConcretizations do
    let conc ← ConcretizationData.create nm eConcrete
    modify fun st => { st with concretizations := st.concretizations.insert nm conc }

  let fcs := (← get).foundConcretizables
  for nm in fcs do
    let some conc := (← get).concretizations.find? nm | throwError "internal error, missing concretization '{nm}'"
    tryRewriteEverywhere (mkFVar conc.fvEqVar) (fun ld => ld.isAuxDecl || ld.fvarId == conc.fvEqVar || ld.fvarId == conc.fvEqBody)

  if !fcs.isEmpty then
    loop

/- Algorithm TODOs(WN):
- apply `dsimp`
- `loop`
  - traverse hyps and not just the goal? maybe just the concretization equality hyps,
    in case they expose further concretizations?
  - be more strategic about where to rewrite?
- `concretizeApp`
  - heuristics for when to visit and when to skip?
  - config for what to concretise and what not to?
  - what about `Prop` args?
  - what about mvars in args?
-/
def evalConcretize : ConcretizeM Unit := do
  loop

  -- At the end, clear the hypotheses by replacing them with let-bindings.
  for (nm, conc) in (← get).concretizations do
    let eBody ← conc.getBody
    let fvLet ← liftMetaTacticAux fun mvarId => do
      -- `$concNm := $eBody`
      let (fv, mvarId) ← intro1P (← define mvarId nm (← inferType eBody) eBody)
      return (fv, [mvarId])

    withMainContext do
      -- `var.$concNm = $concNm`
      let eqTp ← mkEq (mkFVar conc.fvVar) (mkFVar fvLet)
      let eq ← mkExpectedTypeHint (mkFVar conc.fvEqBody) eqTp
      tryRewriteEverywhere eq (fun _ => true)

    evalTactic <| ← `(tactic| clear $(mkIdent (`eqBody ++ nm)) $(mkIdent (`eqVar ++ nm)) $(mkIdent (`var ++ nm)))

/-- Recursively finds and replaces concretizations in the goal and the hypotheses.

A *concretization* of a function application `f #[a₁, .., aₙ]` is a new function or constant
with the longest contiguous prefix of concretizable arguments to `f` fixed. An argument
is *concretizable* when:
- it has no free or bound variables (it's closed); and
- it has forward dependencies, or it is a type argument.

TODO(WN):
- we need to handle concrete arguments bound as let declarations
- lift "contiguous" requirement?
- allow concretizing polymorphic lemmas given as parameters to the tactic

For example, `@List.foldl Nat Bool f` has the concretization
  `List.foldl.Nat.bool : (Nat → Bool → Nat) → Nat → List Bool → Nat`
and `@BitVec.xor 8 x y` has the concretization
  `BitVec.xor.8 : BitVec 8 → BitVec 8 → BitVec 8`

NB: In compilers this is *monomorphisation*, but besides types we also concretize dependent
value arguments.

The Coq variant is in `snipe`:
- https://hal.archives-ouvertesfr/hal-03328935/document
- https://github.com/smtcoq/sniper/blob/af7b0d22f496f8e7a0ee6ca495314d80ea2aa881/theories/elimination_polymorphism.v
-/
elab "concretize" : tactic =>
  evalConcretize |>.run' {
    concretizations := Std.RBMap.empty
    cache := DiscrTree.empty
    newConcretizations := Std.RBMap.empty
    foundConcretizables := NameSet.empty
  }

end Smt.Concretize

def generalAdd [Add α] (a b : α) := a + b

set_option trace.smt.debug true in
example : @generalAdd Int _ 3 3 = (6 : Int) := by
  concretize
  rfl

set_option trace.smt.debug true in
example : ([1,2,3] : List Int).foldl Int.add 0 = 6 := by
  concretize
  rfl