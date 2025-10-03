import Lean
import Smt
import Smt.Real
import Lean.Meta.Tactic.Congr

import Smt.Preprocess.BoolAsProp
import Smt.Preprocess.NatAsInt
import Smt.Preprocess.RatAsReal

namespace Smt.Preprocess.SmtTranslate

open Lean Meta

def traceSmtTranslate (r : Except Exception MVarId) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

/--
  Collect free variables of a given type `type` that occur in any of
  the provided expressions `exprs` (target plus visible hypotheses).
-/
def collectFVarsOfType (type : Name) (exprs : Array Expr) : MetaM (Array Expr) := do
  let mut fVars := #[]
  let lctx ← getLCtx

  for localDecl in lctx do
    if localDecl.type.isConstOf type then
      if exprs.any (fun e => e.hasAnyFVar (· == localDecl.fvarId)) then
        fVars := fVars.push localDecl.toExpr

  return fVars

/-- True iff the expression `ty` mentions `Nat` anywhere (recurses through Π/λ/apps). -/
def containsNat (ty : Expr) : Bool :=
  match ty with
  | .const ``Nat _ => true
  | .app f a => containsNat f || containsNat a
  | .forallE _ t b _ => containsNat t || containsNat b
  | .lam _ t b _ => containsNat t || containsNat b
  | _ => false

/--
  Convert every occurrence of `Nat` inside a type expression into `Int`.
  This preserves the Π/λ structure but changes domains/codomains where needed.
-/
partial def convertNatToInt (ty : Expr) : MetaM Expr :=
  match ty with
  | .const ``Nat _ => pure (mkConst ``Int [])
  | .app f a => do
    let f' ← convertNatToInt f
    let a' ← convertNatToInt a
    pure (mkApp f' a')
  | .forallE n t b bi => do
    let t' ← convertNatToInt t
    withLocalDecl n bi t' fun x => do
      let b' ← convertNatToInt (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .lam n t b bi => do
    let t' ← convertNatToInt t
    withLocalDecl n bi t' fun x => do
      let b' ← convertNatToInt (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | _ => pure ty

/-- Collect the sequence of Π-domains from a function type (left to right). -/
partial def collectDomainTypes (ty : Expr) : Array Expr :=
  match ty with
  | .forallE _ domain body _ =>
    let rest := collectDomainTypes body
    #[domain] ++ rest
  | _ => #[]

/-- Peel all Π-binders to get the final codomain of a function type. -/
partial def getFinalCodomain (ty : Expr) : Expr :=
  match ty with
  | .forallE _ _ body _ => getFinalCodomain body
  | _ => ty

/--
  Given a function `origFn : α₁ → … → αₙ → β`, synthesize an `Int`-domain version:
  - the new type replaces every occurrence of `Nat` in domains and codomain with `Int`;
  - the body re-applies `origFn` to arguments, converting back to `Nat` where the
    original domain required it, and casts results from `Nat` to `Int` if needed.

  Returns the new type and the lambda implementing it.
-/
def createTransformedFunction (origFn : Expr) (origType : Expr) : MetaM (Expr × Expr) := do
  let domains := collectDomainTypes origType
  let codomain := getFinalCodomain origType

  let newDomains ← domains.mapM convertNatToInt
  let newCodomain ← convertNatToInt codomain

  let newType ← newDomains.foldrM (fun dom acc => mkArrow dom acc) newCodomain

  -- Build the lambda over Int-typed arguments
  let buildLambda (argTypes : Array Expr) (_ : Expr) : MetaM Expr := do
    let rec buildRec : (idx : Nat) → (localVars : Array Expr) → MetaM Expr := fun idx localVars => do
      if idx >= argTypes.size then
        -- Apply origFn; coerce Int→Nat where the original domains were Nat
        let origDomains := collectDomainTypes origType
        let convertedArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
          let varType ← inferType var
          if varType.isConstOf ``Int && origType.isConstOf ``Nat then
            -- Int→Nat for Nat domains
            mkAppOptM ``Int.toNat #[var]
          else
            pure var
        let applied := convertedArgs.foldl (fun acc arg => mkApp acc arg) origFn
        -- If result is Nat, cast to Int
        let appliedType ← inferType applied
        if appliedType.isConstOf ``Nat then
          mkAppOptM ``Nat.cast #[mkConst ``Int [], none, applied]
        else
          pure applied
      else
        let argType := argTypes[idx]!
        withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
          let newLocalVars := localVars.push localVar
          let bodyExpr ← buildRec (idx + 1) newLocalVars
          mkLambdaFVars #[localVar] bodyExpr
    termination_by idx => argTypes.size - idx
    buildRec 0 #[]

  let lambdaExpr ← buildLambda newDomains newCodomain
  pure (newType, lambdaExpr)

/--
  Collect free variables whose types mention `Nat` anywhere (including inside
  arrows), restricting to those that occur in the provided expressions.
-/
def collectFVarsWithNat (exprs : Array Expr) : MetaM (Array Expr) := do
  let mut fVars := #[]
  let lctx ← getLCtx

  for localDecl in lctx do
    if containsNat localDecl.type then
      if exprs.any (fun e => e.hasAnyFVar (· == localDecl.fvarId)) then
        fVars := fVars.push localDecl.toExpr

  return fVars

/--
  Collect free variables that have a function type with `Nat` domain, i.e.
  variables of type `Nat → Prop`, and that actually occur in the given expressions.
-/
def collectFVarsOfNatDomain (exprs : Array Expr) : MetaM (Array Expr) := do
  let mut fVars := #[]
  let lctx ← getLCtx

  for localDecl in lctx do
    if localDecl.type.isArrow then
      let domain := localDecl.type.bindingDomain!
      if domain.isConstOf ``Nat then
        if exprs.any (fun e => e.hasAnyFVar (· == localDecl.fvarId)) then
          fVars := fVars.push localDecl.toExpr

  return fVars

/-- Sort free variables by their user-facing names for deterministic behavior. -/
def sortFVars (fVars : Array Expr) : MetaM (Array Expr) := do
  let varNames ← fVars.mapM fun var => do
    let name ← var.fvarId!.getUserName
    return (name, var)
  let sortedVars := varNames.qsort fun (nameA, _) (nameB, _) => nameA.toString < nameB.toString
  let sortedVars := sortedVars.map (·.2)
  return sortedVars

/--
  Traverse an expression and collect arguments `a : Nat` from occurrences
  of `p a` where `p` ranges over the supplied `Nat → Prop` free variables.

  Implemented at top-level so we can use a `termination_by` on the helper.
-/
partial def collectNatArgsFromAux (natDomainFVars : Array Expr) (acc : Array Expr) (e : Expr) : MetaM (Array Expr) := do
  match e with
  | .app f a =>
    let acc ← collectNatArgsFromAux natDomainFVars acc f
    let acc ← collectNatArgsFromAux natDomainFVars acc a
    if !a.hasLooseBVars then
      let matched := match f with
        | .fvar fid => natDomainFVars.any (fun v => v.fvarId! == fid)
        | _ => false
      if matched then
        try
          if (← inferType a).isConstOf ``Nat then
            return acc.push a
        catch _ =>
          return acc
    return acc
  | .lam n t b i => withLocalDecl n i t fun x => collectNatArgsFromAux natDomainFVars acc (b.instantiate1 x)
  | .forallE n t b i => withLocalDecl n i t fun x => collectNatArgsFromAux natDomainFVars acc (b.instantiate1 x)
  | .letE n t v b _ =>
    let acc ← collectNatArgsFromAux natDomainFVars acc t
    let acc ← collectNatArgsFromAux natDomainFVars acc v
    withLetDecl n t v fun x => collectNatArgsFromAux natDomainFVars acc (b.instantiate1 x)
  | .mdata _ e' => collectNatArgsFromAux natDomainFVars acc e'
  | .proj _ _ e' => collectNatArgsFromAux natDomainFVars acc e'
  | _ => pure acc

/--
  Add nonnegativity facts to the context for each concrete `Nat` argument we
  can discover in propositional hypotheses, and arrange local rewrite lemmas to
  canonicalize occurrences `p w` with `w : Nat`.

  High-level steps:
  1. Re-resolve the current `Nat → Prop` variables (fvars may have changed).
  2. Scan each propositional hypothesis and collect arguments `a : Nat` from
     occurrences `p a`; assert `0 ≤ (a : Int)` for each.
  3. Revert those lemmas to place them before the goal (layout management).
  4. For each `p` and each local `w : Nat`, assert a tiny local lemma
     `p w = p (w : Int).toNat` so that simp can rewrite only those occurrences.
  5. Run a bounded simp pass with these locals and then clean them up.
-/
def addNonNegToHypotheses (mv : MVarId) (sortedNatDomainVars : Array Expr) : MetaM MVarId :=
  mv.withContext do
    -- Refresh Nat→Prop fvars: earlier revert/intro/simp may have changed fvar ids
    let currentNatDomainFVars ← do
      let lctx ← getLCtx
      let mut fvs := #[]
      for localDecl in lctx do
        if localDecl.type.isArrow then
          let domain := localDecl.type.bindingDomain!
          if domain.isConstOf ``Nat then
            if sortedNatDomainVars.any (· == localDecl.toExpr) then
              fvs := fvs.push localDecl.toExpr
      pure fvs

    -- Collect Nat arguments `a` found in heads `p a` with `p : Nat → Prop`
    let collectNatArgsFrom : Expr → MetaM (Array Expr) :=
      fun e => collectNatArgsFromAux currentNatDomainFVars #[] e

    -- For each propositional hypothesis, assert `0 ≤ (a : Int)` for each such `a`
    let initialFVars := (← mv.getDecl).lctx.getFVarIds
    let mut newMv := mv
    let mut newHyps : Array FVarId := #[]

    for fvarId in initialFVars do
      let decl ← fvarId.getDecl
      if decl.isImplementationDetail then continue
      if ¬(← isProp decl.type) then continue

      let args ← collectNatArgsFrom decl.type
      for a in args do
        let nonNegProof ← mkAppM ``Int.ofNat_nonneg #[a]
        let nonNegType ← inferType nonNegProof

        -- Base new hypothesis name on the argument when available
        let baseName ← match a with
          | .fvar fid => do
            let n ← fid.getUserName
            pure (n.appendAfter "_nonneg")
          | _ => pure (decl.userName.appendAfter "_nonneg")
        -- Avoid clashes with an index suffix
        let hypName := baseName.appendAfter s!"_{newHyps.size}"

        let mv' ← newMv.assert hypName nonNegType nonNegProof
        let (hFVarId, mv'') ← mv'.intro1P
        newMv := mv''
        newHyps := newHyps.push hFVarId

    -- Move the newly introduced facts before the goal (layout)
    if !newHyps.isEmpty then
      (_, newMv) ← newMv.revert newHyps

    -- Specialize tiny cast lemmas only at local `w : Nat` so simp can rewrite those occurrences
    let mut mvC := newMv
    let mut castLemmaFVars : Array FVarId := #[]
    let natVars ← mvC.withContext do
      let lctx ← getLCtx
      let mut fvs := #[]
      for d in lctx do
        if d.isImplementationDetail then continue
        if d.type.isConstOf ``Nat then
          fvs := fvs.push d.toExpr
      pure fvs
    for p in currentNatDomainFVars do
      let pType ← inferType p
      let pCodomain := pType.getForallBody
      if pCodomain.isProp then
        let pName ← p.fvarId!.getUserName
        for w in natVars do
          let wName ← w.fvarId!.getUserName
          let dcProof ← mkAppM ``doubleCast #[p, w]
          let dcType ← inferType dcProof
          let mv' ← mvC.assert (pName.appendAfter s!"_doubleCast_{wName}") dcType dcProof
          let (dcFVar, mv'') ← mv'.intro1P
          mvC := mv''
          castLemmaFVars := castLemmaFVars.push dcFVar

    -- Use just these locals for a bounded simp pass
    let simpTheorems ← mvC.withContext do
      castLemmaFVars.foldlM (fun st f => st.addTheorem (.fvar f) (mkFVar f)) {}
    let cfg : Meta.Simp.Config := { maxSteps := 10000, singlePass := true }
    let ctx ← Meta.Simp.mkContext cfg simpTheorems

    -- Bounded simp with tracing; fall back to the original goal if no progress
    let newMv1 ← withOptions
      (fun o => o.setBool `trace.Meta.simp true
                    |>.setBool `trace.Meta.simp.rewrite true
                    |>.setBool `trace.Meta.simp.config true
                    |>.setNat `trace.depth 3
                    |>.setNat `maxHeartbeats 200000) do
      match ← Meta.simpTarget mvC ctx with
      | (some mv', _) => pure mv'
      | _ => pure mvC

    -- Clean up local cast lemmas
    if !castLemmaFVars.isEmpty then
      let mvClean ← newMv1.tryClearMany castLemmaFVars
      return mvClean
    else
      return newMv1


/--
  Main preprocessing and translation pass used by `smt_translate`.

  Rough outline of the pipeline:
  - Normalize boolean equalities to propositional equalities.
  - Collect Bool, Rat, Nat, and Nat→Prop variables that occur in the goal/context.
  - Temporarily revert propositional hypotheses; preprocess bounded quantifiers
    using the `Nat.as_int` lemmas.
  - Add structural hypotheses:
    • `x = a / b` witnesses for `Rat` variables,
    • `0 ≤ (x : Int)` for each `Nat` variable,
    • extra nonnegativity facts discovered inside propositional hypotheses.
  - For each function mentioning `Nat`, define an `Int`-domain version `f'` and
    assert both definitional and unfolding lemmas usable by simp. If the codomain
    mentions `Nat`, also assert a generic nonnegativity lemma for `f'`.
  - Run the main simp call with curated theorems and simprocs to eliminate casts.
  - Clean up temporary lemmas, revert structural hypotheses, try a final
    `Int.toNat_of_nonneg` normalization, generalize away Bool/Rat/Nat locals,
    then re-introduce hypotheses and clear the original variables.
-/
def smt_translate (mv' : MVarId) : MetaM MVarId := withTraceNode `smt.reconstruct.smt_translate traceSmtTranslate do
  trace[debug] m!"initial goal: {mv'}"

  let mut mv := mv'

  -- Normalize boolean equalities to propositional equalities when possible
  let r? ← try (do pure (some (← mv.rewrite (← mv.getType) (mkConst ``Bool.eq_iff_iff []) false))) catch _ => pure none
  mv ← match r? with
    | some r => mv.replaceTargetEq r.eNew r.eqProof
    | none   => pure mv

  trace[debug] m!"bool to prop equality: {mv}"

  let target ← mv.getType

  -- Accumulate the target and non-implementation hyps for variable discovery
  let allExprs ← mv.withContext do
    let mut exprs := #[target]
    let lctx ← getLCtx
    for localDecl in lctx do
      if ¬localDecl.isImplementationDetail then
        exprs := exprs.push localDecl.type
    return exprs

  let targetBoolVars ← collectFVarsOfType ``Bool allExprs
  let sortedBoolVars ← sortFVars targetBoolVars

  let targetRatVars ← collectFVarsOfType ``Rat allExprs
  let sortedRatVars ← sortFVars targetRatVars

  let targetNatVars ← collectFVarsOfType ``Nat allExprs
  let sortedNatVars ← sortFVars targetNatVars

  let targetNatDomainVars ← collectFVarsOfNatDomain allExprs
  let sortedNatDomainVars ← sortFVars targetNatDomainVars

  let targetNatFunctionVars ← collectFVarsWithNat allExprs
  let sortedNatFunctionVars ← sortFVars targetNatFunctionVars

  -- Temporarily revert all propositional hypotheses
  let fvarIds ← mv.withContext do getPropHyps

  -- Record their names before reverting (fvar ids will change)
  let propNames ← mv.withContext do
    fvarIds.mapM (·.getUserName)

  (_, mv) ← mv.revert fvarIds

  trace[debug] m!"pop all propositional hypotheses: {mv}"

  let preProcessingTheorems := [``Nat.forall_as_int, ``Nat.exists_as_int]
  let simpPreProcessingTheorems ← preProcessingTheorems.foldrM (fun n a => a.addTheorem (.decl n) (.const n [])) {}
  let ctx ← Meta.Simp.mkContext {} simpPreProcessingTheorems
  let (some mv', _) ← Meta.simpTarget mv ctx | throwError "failed to preprocess goal:{mv}"
  mv := mv'

  trace[debug] m!"preprocess quantifiers: {mv}"

  let mut structuralHypotheses : Array FVarId := #[]

  -- For each `x : Rat`, assert a witness equation `x = a / b` with `a b : Int`
  for ratVar in sortedRatVars do
    let varName ← ratVar.fvarId!.getUserName
    let divProof ← mkAppOptM ``Rat.cast_eq_div_int #[ratVar]
    let divType ← inferType divProof
    mv ← mv.assert (varName.appendAfter "_rat") divType divProof
    let (fVarId, mv') ← mv.intro (varName.appendAfter "_rat")
    structuralHypotheses := structuralHypotheses.push fVarId
    mv := mv'

  -- For each `x : Nat`, assert `0 ≤ (x : Int)`
  for natVar in sortedNatVars do
    let varName ← natVar.fvarId!.getUserName
    -- Target type: (x : Int) ≥ 0
    let xInt ← mkAppOptM ``Nat.cast #[mkConst ``Int [], none, natVar]
    let zeroInt := mkIntLit 0
    let nonNegType ← mkAppOptM ``GE.ge #[mkConst ``Int [], none, xInt, zeroInt]
    -- Proof term: 0 ≤ (x : Int)
    let nonNegProof ← mkAppOptM ``Int.zero_le_ofNat #[natVar]
    mv ← mv.assert (varName.appendAfter "_nonneg") nonNegType nonNegProof
    let (fVarId, mv') ← mv.intro (varName.appendAfter "_nonneg")
    structuralHypotheses := structuralHypotheses.push fVarId
    mv := mv'

  mv ← addNonNegToHypotheses mv sortedNatDomainVars

  trace[debug] m!"rat/nat structural hypotheses: {mv}"

  -- For each function mentioning Nat, define an Int-domain version `f'` and its lemmas; add nonnegativity if codomain mentions Nat
  let mut introducedIntFns : Array FVarId := #[]
  let mut introducedSimpLemmas : Array FVarId := #[]

  -- Re-resolve function variables by user name to avoid stale fvar ids
  let currentNatFunctionVars ← mv.withContext do
    let lctx ← getLCtx
    let mut fvs := #[]
    for localDecl in lctx do
      -- Only process functions (arrows) that contain Nat
      if localDecl.type.isArrow && containsNat localDecl.type then
        if sortedNatFunctionVars.any (fun origVar =>
          -- Match by user name since fvar ids may have changed
          origVar.isFVar &&
          localDecl.toExpr.isFVar &&
          origVar.fvarId! == localDecl.fvarId) then
          fvs := fvs.push localDecl.toExpr
    pure fvs

  for natFn in currentNatFunctionVars do
    let varName ← natFn.fvarId!.getUserName
    let ty ← inferType natFn
    if !ty.isArrow then continue

    -- Use the new multi-argument transformation
    let (newVarType, lambdaExpr) ← createTransformedFunction natFn ty
    let newVarName := varName.appendAfter "'"
    mv ← mv.define newVarName newVarType lambdaExpr
    let (newVarFVarId, mv1) ← mv.intro1P
    let newVarExpr := mkFVar newVarFVarId

    -- Create definitional theorem for the new function
    let (mv2, defFVarId) ← mv1.withContext do
      let domains := collectDomainTypes ty
      let newDomains ← domains.mapM convertNatToInt
      let codomain := getFinalCodomain ty

      -- Build type: ∀ x₁ ... xₙ : Int, (converted original application) = f' x₁ ... xₙ
      let buildDefType (argTypes : Array Expr) : MetaM Expr := do
        let rec buildDefRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
          if idx >= argTypes.size then
            -- Build LHS: original function applied to converted arguments
            let origDomains := collectDomainTypes ty
            let convertedArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
              let varType ← inferType var
              if varType.isConstOf ``Int && origType.isConstOf ``Nat then
                mkAppOptM ``Int.toNat #[var]
              else
                pure var
            let lhsApplied := convertedArgs.foldl (fun acc arg => mkApp acc arg) natFn
            let lhs ← if codomain.isConstOf ``Nat then
              mkAppOptM ``Nat.cast #[mkConst ``Int [], none, lhsApplied]
            else
              pure lhsApplied
            -- Build RHS: new function applied to Int arguments
            let rhs := localVars.foldl (fun acc arg => mkApp acc arg) newVarExpr
            mkEq lhs rhs
          else
            let argType := argTypes[idx]!
            withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
              let newLocalVars := localVars.push localVar
              let bodyExpr ← buildDefRec (idx + 1) newLocalVars
              mkForallFVars #[localVar] bodyExpr
        termination_by argTypes.size - idx
        buildDefRec 0 #[]
      let defType ← buildDefType newDomains

      -- Build proof (reflexivity)
      let buildDefProof (argTypes : Array Expr) : MetaM Expr := do
        let rec buildProofRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
          if idx >= argTypes.size then
            -- The definition is definitionally equal, so reflexivity works
            let origDomains := collectDomainTypes ty
            let convertedArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
              let varType ← inferType var
              if varType.isConstOf ``Int && origType.isConstOf ``Nat then
                mkAppOptM ``Int.toNat #[var]
              else
                pure var
            let lhsApplied := convertedArgs.foldl (fun acc arg => mkApp acc arg) natFn
            let lhs ← if codomain.isConstOf ``Nat then
              mkAppOptM ``Nat.cast #[mkConst ``Int [], none, lhsApplied]
            else
              pure lhsApplied
            Meta.mkEqRefl lhs
          else
            let argType := argTypes[idx]!
            withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
              let newLocalVars := localVars.push localVar
              let bodyExpr ← buildProofRec (idx + 1) newLocalVars
              mkLambdaFVars #[localVar] bodyExpr
        termination_by argTypes.size - idx
        buildProofRec 0 #[]
      let defProof ← buildDefProof newDomains

      let mvDef ← mv1.assert (newVarName.appendAfter "_def") defType defProof
      let (defFVarId, mvDef') ← mvDef.intro1P
      return (mvDef', defFVarId)

    -- Also create an unfolding theorem usable as `simp` lemma: ∀ x₁ ... xₙ, f' x₁ ... xₙ = (converted original application)
    let (mv2_unf, unfoldFVarId) ← mv2.withContext do
      let origDomains := collectDomainTypes ty
      let paramTypes ← origDomains.mapM (fun oty => if oty.isConstOf ``Nat then pure oty else convertNatToInt oty)
      let codomain := getFinalCodomain ty

      let buildUnfoldType (argTypes : Array Expr) : MetaM Expr := do
        let rec buildUnfoldTypeRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
          if idx >= argTypes.size then
            let convertedArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
              let varType ← inferType var
              if varType.isConstOf ``Int && origType.isConstOf ``Nat then
                mkAppOptM ``Int.toNat #[var]
              else
                pure var
            let rhsApplied := convertedArgs.foldl (fun acc arg => mkApp acc arg) natFn
            let rhs ← if codomain.isConstOf ``Nat then
              mkAppOptM ``Nat.cast #[mkConst ``Int [], none, rhsApplied]
            else
              pure rhsApplied
            -- Build LHS: f' applied to Int/Nat-casted args
            let lhsArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
              if origType.isConstOf ``Nat then
                mkAppOptM ``Nat.cast #[mkConst ``Int [], none, var]
              else
                pure var
            let lhs := lhsArgs.foldl (fun acc arg => mkApp acc arg) newVarExpr
            mkEq rhs lhs
          else
            let argType := argTypes[idx]!
            withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
              let newLocalVars := localVars.push localVar
              let bodyExpr ← buildUnfoldTypeRec (idx + 1) newLocalVars
              mkForallFVars #[localVar] bodyExpr
        termination_by argTypes.size - idx
        buildUnfoldTypeRec 0 #[]
      let unfoldType ← buildUnfoldType paramTypes

      let buildUnfoldProof (argTypes : Array Expr) : MetaM Expr := do
        let rec buildUnfoldProofRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
          if idx >= argTypes.size then
            -- Target is rhs = lhs; use reflexivity on lhs (f' applied to casted args)
            let lhsArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
              if origType.isConstOf ``Nat then
                mkAppOptM ``Nat.cast #[mkConst ``Int [], none, var]
              else
                pure var
            let lhs := lhsArgs.foldl (fun acc arg => mkApp acc arg) newVarExpr
            Meta.mkEqRefl lhs
          else
            let argType := argTypes[idx]!
            withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
              let newLocalVars := localVars.push localVar
              let bodyExpr ← buildUnfoldProofRec (idx + 1) newLocalVars
              mkLambdaFVars #[localVar] bodyExpr
        termination_by argTypes.size - idx
        buildUnfoldProofRec 0 #[]
      let unfoldProof ← buildUnfoldProof paramTypes

      let mvUnfold ← mv2.assert (newVarName.appendAfter "_unfold") unfoldType unfoldProof
      let (unfoldFVarId, mvUnfold') ← mvUnfold.intro1P
      return (mvUnfold', unfoldFVarId)

    -- Defer simp with the two theorems to the global simp phase; keep them in context for now.
    let mv3_afterDefs := mv2_unf
    introducedSimpLemmas := introducedSimpLemmas.push defFVarId
    introducedSimpLemmas := introducedSimpLemmas.push unfoldFVarId

    -- If codomain contains Nat, assert nonnegativity lemmas for f'
    mv ←
      if containsNat (getFinalCodomain ty) then
        mv3_afterDefs.withContext do
          let domains := collectDomainTypes ty
          let newDomains ← domains.mapM convertNatToInt

          -- Build nonnegativity type: ∀ x₁ ... xₙ : Int, (∀ i, xᵢ ≥ 0) → f' x₁ ... xₙ ≥ 0
          let buildNonnegType (argTypes : Array Expr) : MetaM Expr := do
            let rec buildNonnegRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
              if idx >= argTypes.size then
                -- Build hypotheses: all Int arguments are nonnegative
                let zeroInt := mkIntLit 0
                let geHyps ← localVars.mapM fun var => do
                  mkAppOptM ``GE.ge #[some (mkConst ``Int []), none, some var, some zeroInt]
                let allGeHyps ← geHyps.foldrM (fun hyp acc => mkArrow hyp acc)
                  (← do
                    let fx := localVars.foldl (fun acc arg => mkApp acc arg) newVarExpr
                    mkAppOptM ``GE.ge #[some (mkConst ``Int []), none, some fx, some zeroInt])
                pure allGeHyps
              else
                let argType := argTypes[idx]!
                withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
                  let newLocalVars := localVars.push localVar
                  let bodyExpr ← buildNonnegRec (idx + 1) newLocalVars
                  mkForallFVars #[localVar] bodyExpr
            termination_by argTypes.size - idx
            buildNonnegRec 0 #[]
          let nonnegType ← buildNonnegType newDomains

          -- Build proof using Int.ofNat_zero_le
          let buildNonnegProof (argTypes : Array Expr) : MetaM Expr := do
            let rec buildNonnegProofRec (idx : Nat) (localVars : Array Expr) : MetaM Expr := do
              if idx >= argTypes.size then
                -- Build proof body
                let zeroInt := mkIntLit 0
                let geHyps ← localVars.mapM fun var => do
                  mkAppOptM ``GE.ge #[some (mkConst ``Int []), none, some var, some zeroInt]
                let rec buildHypLambdas (hypIdx : Nat) (hypVars : Array Expr) : MetaM Expr := do
                  if hypIdx >= geHyps.size then
                    -- Use the original function application and Int.ofNat_zero_le
                    let origDomains := collectDomainTypes ty
                    let convertedArgs ← localVars.zip origDomains |>.mapM fun (var, origType) => do
                      if origType.isConstOf ``Nat then
                        mkAppOptM ``Int.toNat #[some var]
                      else
                        pure var
                    let origApplied := convertedArgs.foldl (fun acc arg => mkApp acc arg) natFn
                    mkAppM ``Int.ofNat_zero_le #[origApplied]
                  else
                    withLocalDecl (Name.mkSimple s!"h{hypIdx}") BinderInfo.default geHyps[hypIdx]! fun hypVar => do
                      let newHypVars := hypVars.push hypVar
                      let bodyExpr ← buildHypLambdas (hypIdx + 1) newHypVars
                      mkLambdaFVars #[hypVar] bodyExpr
                termination_by geHyps.size - hypIdx
                buildHypLambdas 0 #[]
              else
                let argType := argTypes[idx]!
                withLocalDecl (Name.mkSimple s!"x{idx}") BinderInfo.default argType fun localVar => do
                  let newLocalVars := localVars.push localVar
                  let bodyExpr ← buildNonnegProofRec (idx + 1) newLocalVars
                  mkLambdaFVars #[localVar] bodyExpr
            termination_by argTypes.size - idx
            buildNonnegProofRec 0 #[]
          let nonnegProof ← buildNonnegProof newDomains

          let mvNon ← mv3_afterDefs.assert (newVarName.appendAfter "_nonneg") nonnegType nonnegProof
          let (_, mvNon') ← mvNon.intro1P
          pure mvNon'
      else
        pure mv3_afterDefs
    introducedIntFns := introducedIntFns.push newVarFVarId
    introducedIntFns := introducedIntFns.push defFVarId

  trace[debug] m!"introduce new nat functions: {mv}"

  -- Main simp translation set (Bool/Int/Rat casts and comparisons)
  let ns := [
    ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true2, ``Bool.iff_eq_true, ``Bool.xor_eq_true, ``Bool.eq_eq_true, ``Bool.eq_self, ``Bool.true_eq_false, ``Bool.false_eq_true, ``Prop.eq_true, ``Prop.eq_false,

    ``Int.natCast_add, ``Int.natCast_sub2, ``Int.natCast_mul, ``Int.natCast_ediv, ``Int.natCast_emod, ``Int.ofNat_eq, ``Int.ofNat_le2, ``Int.ofNat_lt2, ``Int.ofNat_ge, ``Int.ofNat_gt, ``Int.ofNat_ne, ``Nat.cast_zero, ``Nat.cast_one, ``Nat.cast_ofNat, ``Int.natSub.eq_1, ``Int.toNat_of_nonneg, ``Int.ofNat_eq_coe,

    ``Rat.cast_add, ``Rat.cast_sub, ``Rat.cast_mul, ``Rat.cast_div, ``Rat.cast_neg, ``Rat.cast_inv, ``Rat.cast_eq, ``Rat.cast_le, ``Rat.cast_lt, ``Rat.cast_ge, ``Rat.cast_gt, ``Rat.cast_ne, ``Rat.cast_zero, ``Rat.cast_one, ``Rat.cast_ofNat,
  ]
  let simpTheorems ← mv.withContext do
    let base ← ns.foldrM (fun n a => a.addTheorem (.decl n) (.const n [])) {}
    introducedSimpLemmas.foldlM (fun st f => st.addTheorem (.fvar f) (mkFVar f)) base
  let ctx ← Meta.Simp.mkContext {} simpTheorems
  let onlySimprocs ← do
    let s : Lean.Meta.Simp.SimprocsArray := #[]
    let s ← Lean.Meta.Simp.SimprocsArray.add s ``Int.reduceToNat true
    Lean.Meta.Simp.SimprocsArray.add s ``Int.reduceToNat false
  let (some mv', _) ← Meta.simpTarget mv ctx onlySimprocs | throwError "failed to translate goal:{mv}"
  mv := mv'

  trace[debug] m!"main simp call: {mv}"

  -- Drop temporary simp lemmas
  mv ← mv.tryClearMany introducedSimpLemmas

  trace[debug] m!"clear temporary simp lemmas: {mv}"

  -- Preserve structural hypothesis names before reverting
  let structuralNames ← mv.withContext do
    structuralHypotheses.mapM (·.getUserName)

  (_, mv) ← mv.revert structuralHypotheses

  trace[debug] m!"revert structural hypotheses: {mv}"

  -- Try a focused `Int.toNat_of_nonneg` pass to kill remaining double casts
  mv ← mv.withContext do
    try
      let goals ← Lean.Elab.Term.TermElabM.run' do
        Lean.Elab.Tactic.run mv do
          Lean.Elab.Tactic.evalTactic (← `(tactic| try simp +contextual only [Int.toNat_of_nonneg] at *))

      match goals with
      | [] =>
        -- Goal was solved completely, create a solved goal
        let solvedMv ← Meta.mkFreshExprMVar (mkConst ``True)
        let _ ← solvedMv.mvarId!.assign (mkConst ``True.intro)
        pure solvedMv.mvarId!
      | [newMv] =>
        pure newMv
      | _ =>
        pure goals[0]!
    catch _ =>
      -- If anything fails, just continue with the original goal
      return mv

  trace[debug] m!"attempt to rewrite double cast: {mv}"

  for boolVar in sortedBoolVars do
    let varName ← boolVar.fvarId!.getUserName
    let eqExpr ← mkEq boolVar (mkConst ``true)
    (_, mv) ← mv.generalize #[{ expr := eqExpr, xName? := varName }]

  for ratVar in sortedRatVars do
    let varName ← ratVar.fvarId!.getUserName
    let castExpr ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, ratVar]
    (_, mv) ← mv.generalize #[{ expr := castExpr, xName? := varName }]

  for natVar in sortedNatVars do
    let varName ← natVar.fvarId!.getUserName
    let castExpr ← mkAppOptM ``Nat.cast #[mkConst ``Int [], none, natVar]
    (_, mv) ← mv.generalize #[{ expr := castExpr, xName? := varName }]

  trace[debug] m!"generalizations: {mv}"

  -- Re-introduce props and structural facts with original names
  (_, mv) ← mv.introN (structuralNames ++ propNames).size (structuralNames ++ propNames).toList

  trace[debug] m!"reintroduce propositional and structural hyps: {mv}"

  -- Clear original Bool/Rat/Nat variables; keep generalized/casted forms
  mv ← mv.tryClearMany (sortedRatVars.map (·.fvarId!) ++ sortedNatVars.map (·.fvarId!) ++ sortedBoolVars.map (·.fvarId!))

  trace[debug] m!"final state after clearing vars: {mv}"

  return mv

namespace Tactic

syntax (name := smt_translate) "smt_translate" : tactic

open Lean.Elab Tactic in
@[tactic smt_translate] def evalSmtTranslate : Tactic := fun _ => withMainContext do
  let mv ← Tactic.getMainGoal
  let mv ← SmtTranslate.smt_translate mv
  replaceMainGoal [mv]

end Tactic
