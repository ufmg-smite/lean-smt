/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Tactic

namespace Lean.Meta
open Elab Tactic

-- TODO(WN): Might want to expose the `Syntax`-less versions of `Tactic.Rewrite` stuff in core.

def rewriteTarget (e : Expr) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let r ← (← getMainGoal).rewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (e : Expr) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM FVarId := do
  Term.withSynthesize <| withMainContext do
    let localDecl ← fvarId.getDecl
    let rwResult ← (← getMainGoal).rewrite localDecl.type e symm (config := config)
    let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)
    return replaceResult.fvarId

/-- Try to rewrite using `pf : _ = _` at the goal and local declarations matching `pred`. -/
def tryRewriteWhen (pf : Expr) (pred : LocalDecl → Bool) : TacticM Unit := do
  Tactic.withMainContext do
    try Meta.rewriteTarget pf false {}
    catch _ => pure ()
    let lctx ← getLCtx
    for localDecl in lctx do
      if !pred localDecl then continue
      try let _ ← Meta.rewriteLocalDecl pf false localDecl.fvarId {}
      catch _ => pure ()

inductive Location where
  | hyp (nm : Name)
  | goal
  deriving Inhabited, BEq, Repr

def Location.getType (loc : Location) : TacticM Expr :=
  withMainContext do
    match loc with
    | .goal => getMainTarget
    | .hyp nm =>
      let some localDecl := (← getLCtx).findFromUserName? nm
        | throwError "internal error, unknown hypothesis '{nm}'"
      return localDecl.type

def Location.toTacticLocation : Location → Tactic.Location
  | .goal => .targets #[] true
  | .hyp nm => .targets #[mkIdent nm] false

/-- Apply `simp config only [pf]` at the location. Most features are turned
off in the config, so it is more like `rw` with a bit of extra reduction.
It tries to match the kind of definitional matching done by `DiscrTree`. -/
-- TODO(WN): this whole thing is cursed and I have no idea why it works
def Location.simpRwAt (loc : Location) (pf : Expr) : TacticM Unit := do
  let simpTheorems ← ({} : SimpTheorems).addConst `eq_self
  let simpTheorems : SimpTheoremsArray := #[simpTheorems]
  let simpTheorems ← simpTheorems.addTheorem pf
  let ctx := {
    config := {
      zeta := true
      beta := false
      eta := false
      iota := false
      proj := false
      decide := false
    }
    simpTheorems
  }
  Tactic.simpLocation ctx (loc := loc.toTacticLocation)
  let { ctx, .. } ← mkSimpContext Syntax.missing (eraseLocal := false) (kind := .dsimp)
  Tactic.dsimpLocation ctx (loc := loc.toTacticLocation)

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
  deriving Inhabited

def ConcretizationData.create (nm : Name) (eConcrete : Expr) : TacticM ConcretizationData := do
  let conc ← liftMetaTacticAux fun mvarId => do
    let nmVar := nm.modifyBase (· ++ `var)
    let nmEqVar := nm.modifyBase (· ++ `eqVar)
    let nmEqBody := nm.modifyBase (· ++ `eqBody)

    let (#[fvVar, fvEqVar], mvarId) ← mvarId.generalize #[{
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
    let (_, mvarId) ← (← mvarId.assert conc.nmEqBody tpEqBody pfEqBody).intro1P
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

structure Config where
  /-- Set of constant names which should be concretized when found. -/
  concretizeSet : NameSet
  /-- Skip the last let-introduction step when `false.` Useful for debugging the internal
  hypothesis representation. -/
  rewriteWithLets : Bool := true

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
  /-- The concretizations of all polymorphic terms we found. These might or might not already
  have `generalize` hypotheses which we introduce lazily. Rewriting with each must make progress
  on concretizing the goal. -/
  foundConcretizables : NameSet := .empty

abbrev ConcretizeM := StateT State <| ReaderT Config TacticM

def withMainContext (x : ConcretizeM α) : ConcretizeM α := do
  controlAt TacticM fun mapInBase => Tactic.withMainContext (mapInBase x)

def traceLCtx : TacticM Unit := traceCtx `smt.debug.lctx <| Tactic.withMainContext do
  for ld in (← getLCtx) do
    trace[smt.debug.concretize.lctx] "{ld.userName} @ {repr ld.fvarId} : {ld.type} {if ld.isAuxDecl then "(aux)" else ""}"

def getCached? (e : Expr) : ConcretizeM (Option (Name × Nat)) := do
  -- We use `withExtra` as concretizations can be prefixes of the full application.
  let nms ← (←get).cache.getMatchWithExtra e
  if nms.size > 1 then unreachable!
  if let #[(nm, n)] := nms then
    trace[smt.debug.concretize.cache] "hit {e} ↦ {nm}, left {n} args"
    return some (nm, n)
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
    if !(← read).concretizeSet.contains declName then return .visit e

    -- Hits if an application with the same concretization was seen before.
    if let some (nm, _) ← getCached? e then
      foundConcretizable nm
      return .done e

    let info ← getFunInfoNArgs fn args.size
    let mut concreteArgs := #[]
    for (pi, a) in info.paramInfo.zip args do
      let argTp ← inferType a
      -- TODO: This has good results but might be expensive.
      let a' := if !pi.isInstImplicit then ← whnf a else a
      let isConcretizable :=
        !a'.hasLooseBVars ∧ !a'.hasFVar ∧ (argTp.isType ∨ pi.hasFwdDeps ∨ pi.isInstImplicit)
      if isConcretizable then
        concreteArgs := concreteArgs.push (some a')
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
      newConcretizations := .empty
      foundConcretizables := .empty
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
  for nm in fcs.toArray do
    let some conc := (← get).concretizations.find? nm
      | throwError "internal error, missing concretization '{nm}'"
    withMainContext <| tgt.simpRwAt (mkFVar conc.fvEqVar)

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
  - support polymorphic theorems and hyps. go inside them and if we find concretizables
    there, instantiate the whole thing at the concrete args. pass these as list to tactic,
    perhaps also heuristically choose hyps.
- `concretizeApp`
  - what about `Prop` args?
  - what about mvars in args?
-/
def evalConcretize : ConcretizeM Unit := do
  loop

  if !(← read).rewriteWithLets then return

  -- Sort and let-bind concretizations in dependency order.
  let concs ← (← get).concretizations.foldM (init := #[]) fun acc nm conc =>
    return acc.push (nm, conc, ← conc.getBody)
  let concs := concs.qsort fun (_, conc₁, _) (_, _, eBody₂) => eBody₂.hasAnyFVar (· == conc₁.fvVar)

  for (nm, conc, _) in concs do
    -- Note: we must run this again here because the fvars may have changed.
    let eBody ← Tactic.withMainContext conc.getBody
    let fvLet ← liftMetaTacticAux fun mvarId => do
      -- `$concNm := $eBody`
      let (fv, mvarId) ← (← mvarId.define nm (← inferType eBody) eBody).intro1P
      return (fv, [mvarId])

    withMainContext do
      -- `var.$concNm = $concNm`
      let eqTp ← mkEq (mkFVar conc.fvVar) (mkFVar fvLet)
      let declEqBody ← conc.getDeclEqBody
      let eq ← mkExpectedTypeHint declEqBody.toExpr eqTp
      tryRewriteWhen eq fun ld => (`eqBody).isSuffixOf ld.userName.eraseMacroScopes

    evalTactic <| ← `(tactic| clear $(mkIdent (nm ++ `eqBody)) $(mkIdent (nm ++ `eqVar)) $(mkIdent (nm ++ `var)))

/-- Recursively finds and replaces concretizations in the goal and the hypotheses.
We only concretize applications of the constants passed in as tactic arguments.

TODO(WN): heuristics I tried for auto-choosing constants to concretize fail badly. What's a good one?

A *concretization* of a function application `f #[a₁, .., aₙ]` is a new function or constant
with the longest contiguous prefix of concretizable arguments to `f` fixed. An argument
is *concretizable* when:
- it has no free or bound variables (it's closed); and
- it has forward dependencies, or it is a type argument.

TODO(WN):
- lift "contiguous" requirement?

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
elab "concretize" "[" nms:ident,* "]" : tactic => do
  let nms ← (nms : Array Syntax).mapM resolveGlobalConstNoOverloadWithInfo
  let concretizeSet := nms.foldl (init := .empty) (NameSet.insert · ·)
  evalConcretize
    |>.run' { visitSet := #[.goal] }
    |>.run { concretizeSet }

end Smt.Concretize
