/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic
import Lean.Elab.Term

import Smt.Tactic.WHNFSmt

/-! Utilities for handling "equational definitions". An equational definition is an equation
of the form `∀ x₁ ⋯ xₙ, c x₁ ⋯ xₙ = body[x₁,⋯,xₙ]` in the local context, where `c` is either
a global constant or a local variable. The LHS should be fully applied so that the equality
is not at a universally quantified (aka function) type.

These usually start off as copied equational theorems of global constants but are then transformed
to an SMT-compatible form.

Note that equational definitions have an advantage over let-bindings in that we do not need
to justify the termination of `body`. This does however imply that rewriting by an equational
definition may never reach a fixpoint.

## Representation

The equational definition for `foo` is stored as `foo.def` in the local context.

TODO(WN): We could have a custom `smt` tactic mode which provides explicit storage for eqn-defs
and displays them more nicely. -/

namespace Smt
open Lean Meta Elab Term Tactic

/-- The user name of an equational definition for 'nm'. -/
def eqnDefName (nm : Name) : Name :=
  nm ++ `def

def throwNotEqnDef [Monad m] [MonadError m] (e : Expr) : m α :=
  throwError "expected equational definition, got{indentD e}"

/-- Get the head symbol `c` of an equational definition. -/
def getEqnDefHead (eqn : Expr) : MetaM Expr :=
  forallTelescopeReducing eqn fun _ eqn => do
    let some (_, lhs, _) := eqn.eq? | throwNotEqnDef eqn
    return lhs.getAppFn

/-- Get the body of an equational definition as a lambda `fun x₁ ⋯ xₙ => body[x₁,⋯,xₙ]`. -/
def getEqnDefLam (eqn : Expr) : MetaM Expr :=
  forallTelescopeReducing eqn fun args eqn => do
    let some (_, _, body) := eqn.eq? | throwNotEqnDef eqn
    mkLambdaFVars args body

/-- If `nm` has an equational definition, `getEqnDefLam` it. -/
def getEqnDefLamFor? (nm : Name) : MetaM (Option Expr) := do
  let some ld := (← getLCtx).findFromUserName? (eqnDefName nm) | return none
  getEqnDefLam ld.type

/-- Add an equational definition `$nm.def : ∀ x₁ ⋯ xₙ, $nm x₁ ⋯ xₙ = body[x₁,⋯,xₙ]`
for a constant and return the equation's fvar. -/
def addEqnDefForConst (nm : Name) : TacticM FVarId := do
  let some eqnThm ← getUnfoldEqnFor? (nonRec := true) nm
    | throwError "failed to retrieve equation theorem for '{nm}'"
  let eqnInfo ← getConstInfo eqnThm
  let (eqn, pf) ← forallTelescopeReducing eqnInfo.type fun args eqn => do
    let some (_, lhs, body) := eqn.eq? | throwNotEqnDef eqn
    let pf ← mkAppOptM eqnInfo.name (args.map some)
    /- Consider the curried definition
    ```lean
    def baw (a : Int) : Int → Int := Int.add a
    ```
    For this, Lean generates the equational theorem
    ```lean
    ∀ (a : Int), baw a = Int.add a
    ```
    which is transformed by the first `forallTelescope` into `baw a = Int.add a`, an equality
    at a function type. Since we want equational definitions to be fully applied, we need to apply
    a second `forallTelescope` on the type of this equality in order to get `baw a b = Int.add a b`,
    which then gets abstracted into `∀ (a b : Int), baw a b = Int.add a b`. -/
    forallTelescopeReducing (← inferType lhs) fun args' _ => do
      let lhs' ← mkAppOptM' lhs (args'.map some)
      let body' ← mkAppOptM' body (args'.map some)
      let eq ← mkEq lhs' body'
      let pf ← args'.foldlM (init := pf) (mkCongrFun · ·)
      -- Abstract the proof into a lambda with a forall type
      let eqAbstracted ← mkForallFVars (args ++ args') eq
      let pfAbstracted ← mkLambdaFVars (args ++ args') pf
      -- let pfAbstracted ← ensureHasType (some eqAbstracted) pfAbstracted
      return (eqAbstracted, pfAbstracted)

  liftMetaTacticAux fun mvarId => do
    let (fv, mvarId) ← (← mvarId.assert (nm ++ `def) eqn pf).intro1P
    return (fv, [mvarId])

/-- Given `e : tp`, make a local constant `$nm : tp := e` and add an equational definition
`$nm.def : ∀ x₁ ⋯ xₙ, $nm x₁ ⋯ xₙ = e x₁ ⋯ xₙ` for it. Return fvar ids of the constant
and the equation.

`e` is expected to be fully abstracted, i.e. of the form `fun x₁ ⋯ xₙ => body`
where `body` does not have a forall type. -/
def addEqnDefWithBody (nm : Name) (e : Expr) : TacticM (FVarId × FVarId) := do
  let tp ← inferType e
  let fvVar ← liftMetaTacticAux fun mvarId => do
    -- TODO: We have to `define` in order for the proofs to go through, but ideally
    -- we would hide the actual `let` body in the goal state as it's already shown
    -- in the equational definition.
    let (fvVar, mvarId) ← (← mvarId.define nm tp e).intro1P
    return (fvVar, [mvarId])
  
  let (eqn, pf) ← withMainContext <| lambdaTelescope e fun args body => do
    let lhs ← mkAppOptM' (mkFVar fvVar) (args.map some)
    let eqn ← mkEq lhs body
    let pf ← mkEqRefl lhs
    -- Abstract the proof into a lambda with a forall type
    let eqAbstracted ← mkForallFVars args eqn
    let pfAbstracted ← mkLambdaFVars args pf
    -- let pfAbstracted ← ensureHasType (some eqAbstracted) pfAbstracted
    return (eqAbstracted, pfAbstracted)

  liftMetaTacticAux fun mvarId => do
    let (fvEq, mvarId) ← (← mvarId.assert (nm ++ `def) eqn pf).intro1P
    return ((fvVar, fvEq), [mvarId])

/-- Make a new equational definition which specializes an existing one.
We append the pretty-printed concrete args to the original name and define it.
We also assert `$nm.specialization : ∀ x₁ ⋯ xₙ, $nmSpecialized x₁ ⋯ xₙ = $nm c₁ ⋯ cₖ x₁ ⋯ xₙ`,
where `c₁ ⋯ cₙ` are the concrete args, which can be used to rewrite occurrences
into their specialization. This is used for monomorphization. -/
def specializeEqnDef (x : FVarId) (args : Array Expr) : TacticM FVarId := do
  withMainContext do
    let eqn ← inferType (mkFVar x)

    -- Compute specialized body
    let newEqn ← instantiateForall eqn args
    let newLamBody ← getEqnDefLam newEqn
    let newLamBody ← smtOpaqueReduce newLamBody

    -- Compute specialization name
    let ld ← getLocalDecl x
    let some nm := ld.userName.eraseSuffix? `def | throwError "{mkFVar x} is not an eqn def!"
    let nm ← args.foldlM (init := nm) fun nm arg => do
      let txt := toString (← ppExpr arg)
      -- let txt := txt.replace " " "_"
      return nm ++ Name.mkSimple txt

    -- Define the specialization
    let (fvVar, fvEq) ← addEqnDefForLocal nm newLamBody

    -- TODO: these nested withContexts are a bit wonky, can we get a nicer api? `withAddEqnDefForLocal` or something
    withMainContext do
      -- Compute the rewrite helper
      let (eqnRw, pfRw) ← forallTelescope newEqn fun fvArgs newEqn => do
        let some (_, specializedHead, _) := newEqn.eq? | throwNotEqnDef newEqn
        let rhs ← mkAppOptM' (mkFVar fvVar) (fvArgs.map some)
        let eqnRw ← mkEq specializedHead rhs
        let pf ← mkAppOptM' (mkFVar fvEq) (fvArgs.map some)
        let pf ← mkEqSymm pf
        let eqAbstracted ← mkForallFVars fvArgs eqnRw
        let pfAbstracted ← mkLambdaFVars fvArgs pf
        -- TODO: Times out a lot
        --let pfAbstracted ← ensureHasType (some eqAbstracted) pfAbstracted
        return (eqAbstracted, pfAbstracted)

      liftMetaTacticAux fun mvarId => do
        let (fvEq, mvarId) ← intro1P (← assert mvarId (nm ++ `specialization) eqnRw pfRw)
        return (fvEq, [mvarId])

open Lean Meta Elab Tactic in
elab "extract_def" i:ident : tactic => do
  let nm ← resolveGlobalConstNoOverloadWithInfo i
  let _ ← addEqnDefForConst nm

open Lean Meta Elab Tactic in
elab "specialize_def" i:ident "[" ts:term,* "]" : tactic => do
  withMainContext do
    let ld ← getLocalDeclFromUserName i.getId
    let args ← forallTelescopeReducing (← inferType (mkFVar ld.fvarId)) fun args _ => do
      let mut ret : Array Expr := #[]
      for (stx, arg) in ts.getElems.zip args do
        let e ← elabTerm stx (some (← inferType arg))
        ret := ret.push e
      return ret
    let _ ← specializeEqnDef ld.fvarId args

-- Potential:
-- transformEqnDefBody
-- rewriteByEqnDef

end Smt
