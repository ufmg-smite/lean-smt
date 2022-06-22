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

def rewriteLocalDecl (e : Expr) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM FVarId := do
  Term.withSynthesize <| withMainContext do
    let localDecl ← getLocalDecl fvarId
    let rwResult ← rewrite (← getMainGoal) localDecl.type e symm (config := config)
    let replaceResult ← replaceLocalDecl (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)
    return replaceResult.fvarId

/-- Try to rewrite using `pf : _ = _` everywhere except for local declarations matching `skipPred`. -/
-- TODO delete, it's too blunt ?
def tryRewriteEverywhere (pf : Expr) (skipPred : LocalDecl → Bool) : TacticM Unit := do
  Tactic.withMainContext do
    try Meta.rewriteTarget pf false {}
    catch _ => pure ()
    let lctx ← getLCtx
    for localDecl in lctx do
      if skipPred localDecl then continue
      try let _ ← Meta.rewriteLocalDecl pf false localDecl.fvarId {}
      catch _ => pure ()

inductive Location where
  | hyp (nm : Name)
  | goal
  deriving Inhabited, BEq, Repr

def Location.tryRewriteAt (loc : Location) (pf : Expr) : TacticM Unit :=
  withMainContext do
    try
      match loc with
      | .goal => Meta.rewriteTarget pf false {}
      | .hyp nm =>
        if let some localDecl := (← getLCtx).findFromUserName? nm then
          let _ ← Meta.rewriteLocalDecl pf false localDecl.fvarId {}
    catch _ => return ()

def Location.dsimpAt (loc : Location) : TacticM Unit :=
  match loc with
  | .goal => dsimpLocation {} (.targets #[] true)
  | .hyp nm => dsimpLocation {} (.targets #[mkIdent nm] false)

def Location.getType (loc : Location) : TacticM Expr :=
  withMainContext do
    match loc with
    | .goal => getMainTarget
    | .hyp nm =>
      let some localDecl := (← getLCtx).findFromUserName? nm
        | throwError "internal error, unknown hypothesis '{nm}'"
      return localDecl.type

end Lean.Meta

namespace Smt.Concretize

open Lean Elab Meta Tactic

/-- Some crap we need to store while processing the tactic. -/
structure ConcretizationData where
  eConcrete : Expr
  /-- `$nm.var : _` created by `generalize`.
  These should not be rewritten, so we keep the `FVarId`. -/
  fvVar : FVarId
  /-- `$nm.eqVar : $eConcrete = $nm.var` created by `generalize`.
  These should not be rewritten, so we keep the `FVarId`. -/
  fvEqVar : FVarId
  /-- `$nm.eqBody : $nm.var = $eBody`

  We use this equality to simulate a let-binding since it is not easy to rewrite
  in a let-binding body. Note that other concretization steps may recursively rewrite
  in `eBody`, so we only remember the name as the `FVarId` might change. -/
  nmEqBody : Name

def ConcretizationData.create (nm : Name) (eConcrete : Expr) : TacticM ConcretizationData := do
  let conc ← liftMetaTacticAux fun mvarId => do
    let nmVar := nm.modifyBase (· ++ `var)
    let nmEqVar := nm.modifyBase (· ++ `eqVar)
    let nmEqBody := nm.modifyBase (· ++ `eqBody)

    let (#[fvVar, fvEqVar], mvarId) ← Meta.generalize mvarId #[{
        expr := eConcrete
        xName? := nmVar
        hName? := nmEqVar
      }] | throwError "internal error, unexpected generalize fvars"

    let ret := { eConcrete, fvVar, fvEqVar, nmEqBody }
    return (ret, [mvarId])

  -- NB: the second liftMetaTactic is to get the updated goal context
  liftMetaTactic fun mvarId => do
    -- `@f a b` ≡ `(fun x y z w => t) a b` ≡ `fun z w => t[a/x,b/y]`
    let eBody ← withTransparency TransparencyMode.all <| whnf eConcrete
    let tpEqBody ← mkEq (mkFVar conc.fvVar) eBody
    let pfEqBody ← mkEqSymm (mkFVar conc.fvEqVar)
    let (_, mvarId) ← intro1P (← assert mvarId conc.nmEqBody tpEqBody pfEqBody)
    return [mvarId]
  
  return conc

def ConcretizationData.getDeclEqBody (conc : ConcretizationData) : TacticM LocalDecl :=
  withMainContext do
    getLocalDeclFromUserName conc.nmEqBody

def ConcretizationData.getBody (conc : ConcretizationData) : TacticM Expr :=
  withMainContext do
    let localDecl ← conc.getDeclEqBody
    let tp ← inferType localDecl.toExpr
    let some (_, _, eBody) := tp.eq?
      | throwError "internal error, expected equality but got {tp}"
    return eBody

structure State where
  /-- Stores all concretizations and their equality hypotheses. These should be well-formed
  in the goal's local context. -/
  concretizations : Std.RBMap Name ConcretizationData Name.quickCmp := .empty
  /-- Cache of concretization names, lookupable by the concretization. -/
  cache : DiscrTree Name := .empty

  -- Stuff above is a persistent cache. Stuff below changes on every iteration.

  /-- Locations that we should visit next. -/
  visitSet : Array Meta.Location
  /-- New concretizations found. -/
  newConcretizations : Std.RBMap Name Expr Name.quickCmp := .empty
  /-- Names of concretizations corresponding to all polymorphic terms found. These might or might
  not already have `generalize` hypotheses which we introduce lazily. Rewriting with each must make
  progress on concretizing the goal. -/
  foundConcretizables : NameSet := .empty

abbrev ConcretizeM := StateT State TacticM

def withMainContext (x : ConcretizeM α) : ConcretizeM α := do
  controlAt TacticM fun mapInBase => Tactic.withMainContext (mapInBase x)

def traceLCtx : TacticM Unit := traceCtx `smt.debug.lctx <| Tactic.withMainContext do
  for ld in (← getLCtx) do
    trace[smt.debug.concretize.lctx] "{ld.userName} @ {repr ld.fvarId} : {ld.type} {if ld.isAuxDecl then "(aux)" else ""}"

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
    -- let nm ← mkFreshUserName nm

    addNewConcretization nm eConcrete
    foundConcretizable nm

    -- We visit children immediately as concretizing the head partial application `eConcrete`
    -- does not expose new opportunities in the arguments.
    return .visit e

partial def loop : ConcretizeM Unit := traceCtx `smt.debug.concretize.loop do
  if (← get).visitSet.isEmpty then return
  let tgt ← modifyGet fun st =>
    let st' := { st with
      newConcretizations := Std.RBMap.empty
      foundConcretizables := NameSet.empty
      visitSet := st.visitSet.pop
    }
    (st.visitSet.back, st')
  trace[smt.debug.concretize.loop] "visit {repr tgt}"
  
  let _ ← withMainContext <| Meta.transform (← tgt.getType) (m := ConcretizeM) (pre := concretizeApp)

  for (nm, eConcrete) in (← get).newConcretizations do
    let conc ← ConcretizationData.create nm eConcrete
    modify fun st => { st with
      concretizations := st.concretizations.insert nm conc
      visitSet := st.visitSet.push (.hyp conc.nmEqBody)
    }

  let fcs := (← get).foundConcretizables
  for nm in fcs do
    let some conc := (← get).concretizations.find? nm
      | throwError "internal error, missing concretization '{nm}'"
    tgt.tryRewriteAt (mkFVar conc.fvEqVar)
    tgt.dsimpAt

  if !fcs.isEmpty then
    loop

/- Algorithm:
```lean
  let visitSet ← { ⊢ }
  while !visitSet.empty do
    let target ← visitSet.pop
    newConcretizations, concretizationsFound ← findConcretizations target
    for nc in newConcretizations do
      generalize $nm.eqVar : $eConcrete = $nm.var
      have $nm.eqBody : $nm.var = dsimp(whnf($eConcrete))
      visitSet ← visitSet + { $nm.eqBody }
    
    for fc in foundConcretizations do
      rewriteAt tgt $nm.eqVar

  for nm in concretizations do
    let $nm := $eBody
    rw [_ : $nm.var = $nm]
    clear $nm.eqBody, $nm.eqVar, $nm.var
```

Algorithm TODOs(WN):
- `loop`
  - in case of polymorphic hyps, maybe go inside them and if we find something matching
    a known concretization then instantiate the whole thing at the concrete args.
- `concretizeApp`
  - heuristics for when to visit and when to skip?
  - config for what to concretise and what not to?
  - what about `Prop` args?
  - what about mvars in args?
-/
def evalConcretize : ConcretizeM Unit := do
  loop

  -- HACK: When clearing the hypotheses, we rely on the relative ordering of `eqBody hyps to give
  -- us the right rewriting order. We may have to track dependencies manually if this breaks
  withMainContext do
    let mut fvars := #[]
    for ld in ← withMainContext getLCtx do
      if (`eqBody).isSuffixOf ld.userName.eraseMacroScopes then
        fvars := fvars.push ld.fvarId

    for fv in fvars.reverse do
      let nm := (← getLocalDecl fv).userName.eraseMacroScopes.getPrefix
      let some conc := (← get).concretizations.find? nm | throwError "internal error, missing concretization '{nm}'"
      let eBody ← conc.getBody
      let fvLet ← liftMetaTacticAux fun mvarId => do
        -- `$concNm := $eBody`
        let (fv, mvarId) ← intro1P (← define mvarId nm (← inferType eBody) eBody)
          return (fv, [mvarId])

      withMainContext do
        -- `var.$concNm = $concNm`
        let eqTp ← mkEq (mkFVar conc.fvVar) (mkFVar fvLet)
        let declEqBody ← conc.getDeclEqBody
        let eq ← mkExpectedTypeHint declEqBody.toExpr eqTp
        tryRewriteEverywhere eq fun ld => !((`eqBody).isSuffixOf ld.userName.eraseMacroScopes)

      evalTactic <| ← `(tactic| clear $(mkIdent (nm ++ `eqBody)) $(mkIdent (nm ++ `eqVar)) $(mkIdent (nm ++ `var)))

/-- Recursively finds and replaces concretizations in the goal and the hypotheses.

A *concretization* of a function application `f #[a₁, .., aₙ]` is a new function or constant
with the longest contiguous prefix of concretizable arguments to `f` fixed. An argument
is *concretizable* when:
- it has no free or bound variables (it's closed); and
- it has forward dependencies, or it is a type argument.

TODO(WN):
- we need to handle concrete arguments bound as let declarations
- lift "contiguous" requirement?
- allow concretizing polymorphic lemmas given as parameters to the tactic,
  or heuristically.

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
  evalConcretize |>.run' { visitSet := #[.goal] }

end Smt.Concretize

namespace test

def generalAdd [Add α] (a b : α) := a + b

set_option trace.smt.debug true in
example : @generalAdd Int _ 3 3 = (6 : Int) := by
  concretize
  rfl

def BitVec (w : Nat) := Fin (2^w)
protected def BitVec.zero (w : Nat) : BitVec w :=
  ⟨0, Nat.pos_pow_of_pos _ <| by decide⟩
instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩
opaque BitVec.xor {w : Nat} : BitVec w → BitVec w → BitVec w

def polyAdd {w : Nat} : BitVec w → BitVec w → BitVec w :=
  BitVec.xor
def polyDouble {w : Nat} (x : BitVec w) : BitVec w :=
  polyAdd x x

set_option trace.smt.debug true in
example (x y : BitVec 2) : polyDouble (polyAdd x y) = polyDouble (polyAdd y x) := by
  concretize
  sorry

set_option trace.smt.debug true in
example : ([1,2,3] : List Int).foldl Int.add 0 = 6 := by
  -- TODO(WN): everything breaks when `whnf` makes no progress on the concretization body
  concretize
  rfl

end test