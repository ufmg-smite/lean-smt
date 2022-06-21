/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Tactic

namespace Lean.Meta
open Elab Tactic

-- TODO(WN): Might want to expose these syntax-less versions in core.

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

end Lean.Meta

namespace Smt.Concretize

open Lean Elab Meta Tactic

structure State where
  /-- Stores all concretizations and their equality hypotheses `$eConcrete = $nm`,
  if already introduced.

  These should not depend on a local context other than let-decls in the goal's. -/
  concretizations : Std.RBMap Name (Option FVarId × Expr) Name.quickCmp
  /-- Cache of concretization names, lookupable by the concretization. -/
  cache : DiscrTree Name
  /-- In a single iteration of the algorithm, names of concretizations corresponding to all
  polymorphic terms found. These might or might not already have `generalize` hypotheses
  which we introduce lazily. Rewriting with each must make progress on concretizing the goal. -/
  foundConcretizables : NameSet

abbrev ConcretizeM := StateT State TacticM

def foundConcretizable (nm : Name) : ConcretizeM Unit :=
  modify fun st => { st with foundConcretizables := st.foundConcretizables.insert nm }

def getCached? (e : Expr) : ConcretizeM (Option Name) := do
  -- We use `withExtra` as concretizations can be prefixes of the full application.
  let nms ← (←get).cache.getMatchWithExtra e
  if nms.size > 1 then unreachable!
  if let #[(nm, _)] := nms then
    trace[smt.debug.concretize.cache] "hit {e} ↦ {nm}"
    return some nm
  trace[smt.debug.concretize.cache] "miss {e}"
  return none

def addConcretization (nm : Name) (e : Expr) : ConcretizeM Unit := do
  let st ← get
  let cache ← st.cache.insert e nm
  let concretizations := st.concretizations.insert nm (none, e)
  set { st with cache, concretizations }

def withMainContext (x : ConcretizeM α) : ConcretizeM α := do
  controlAt TacticM fun mapInBase => Tactic.withMainContext (mapInBase x)

def concretizeApp (e : Expr) : ConcretizeM TransformStep := do
  trace[smt.debug.concretize.app] "visiting {e}"
  if !e.isApp then return .visit e
  e.withApp fun fn args => do
    let .const declName .. := fn | return .visit e
    -- TODO config for special cases such as this one?
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
      -- TODO what about `Prop` args?
      -- TODO what about mvars?
      let isConcretizable :=
        !a.hasLooseBVars ∧ !a.hasFVar ∧ (argTp.isType ∨ pi.hasFwdDeps)
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

    addConcretization nm eConcrete
    foundConcretizable nm

    -- Even though they may have concretizable subterms, we do not visit children
    -- as they will be taken care of in the next iteration.
    return .done e

def traceLCtx : MetaM Unit :=
    traceCtx `smt.debug.lctx do
      for localDecl in (← getLCtx) do
        trace[smt.debug.concretize.lctx] "{localDecl.userName} : {localDecl.type} {if localDecl.isAuxDecl then "(aux)" else ""})"

partial def evalConcretize : ConcretizeM Unit := do
  go (← getMainTarget)
where go (e : Expr) : ConcretizeM Unit := traceCtx `smt.debug.concretize.go do
  modify fun st => { st with foundConcretizables := NameSet.empty }
  let _ ← withMainContext <| Meta.transform e (m := ConcretizeM) (pre := concretizeApp)
  let fcs := (← get).foundConcretizables
  for nm in fcs do
    let (hypFv?, eConcrete) := (← get).concretizations.find! nm
    let fvEq ← if let some fv := hypFv? then pure fv else
      let fvEq ← withMainContext <| liftMetaTacticAux fun mvarId => do
        -- `$nm : _`
        -- `eqVar.$nm : $eConcrete = $nm`
        let eqVarName := nm.modifyBase (`eqVar ++ ·)
        let (#[_, fvEq], mvarId) ← Meta.generalize mvarId #[{ expr := eConcrete, xName? := nm, hName? := eqVarName }]
          | throwError "unexpected generalize fvars"

        -- `@f a b` ≡ `(fun x y z w => t) a b` ≡ `fun z w => t[a/x,b/y]`
        let eBody ← whnf eConcrete
        -- `eqBody.$nm : $eConcrete = $eBody`
        let eqBodyName := nm.modifyBase (`eqBody ++ ·)
        let tpEqBody ← mkEq eConcrete eBody
        let pfEqBody ← mkEqRefl eConcrete
        let (_, mvarId) ← intro1P (← assert mvarId eqBodyName tpEqBody pfEqBody)
        return (fvEq, [mvarId])

      modify fun st => { st with concretizations := st.concretizations.insert nm (fvEq, eConcrete) }
      pure fvEq

    withMainContext do
      try Meta.rewriteTarget (mkFVar fvEq) false {}
      catch _ => pure ()
      let lctx ← getLCtx
      for localDecl in lctx do
        if localDecl.isAuxDecl || (`eqVar).isPrefixOf localDecl.userName then continue
        try Meta.rewriteLocalDecl (mkFVar fvEq) false localDecl.fvarId {}
        catch _ => pure ()

  if !fcs.isEmpty then
    go (← getMainTarget)
  return

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
    foundConcretizables := NameSet.empty
  }

end Smt.Concretize