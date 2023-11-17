/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.LiftOrNToImp
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

namespace Smt.Reconstruction.Certifying

theorem orFalse : ∀ {A : Prop}, A ∨ False → A := by
  intros a h
  cases h with
  | inl ha => exact ha
  | inr ff => exact False.elim ff
/-
  removeFalse: takes an or-chain ended in `False` and proves
  that it implies the same or-chain without the `False` in the end.
-/
syntax (name := removeFalse) "removeFalse" term "," term : tactic

def removeFalseCore (val type : Expr) : MetaM Expr := do
  let length ← getLength type
  if length > 2 then
    let groupped ← groupPrefixCore val (length - 1)
    mkAppM ``orFalse #[groupped]
  else
    mkAppM ``orFalse #[val]

@[tactic removeFalse] def evalRemoveFalse : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let hypType ← inferType hyp
    let answer ← removeFalseCore hyp hypType
    let mvar ← getMainGoal
    let type ← Meta.inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

def liftOrNToNegMeta (val : Expr) : MetaM Expr := do
  let type ← expandLet (← inferType val)
  let withoutFalse ← removeFalseCore val type
  let type' ← instantiateMVars (← expandLet (← inferType withoutFalse))
  let propsList ← collectPropsInOrChain type'
  let notPropsList := map notExpr propsList
  let propsListExpr := listExpr notPropsList $ Expr.sort Level.zero
  let deMorgan := mkApp (mkConst ``deMorgan₂) propsListExpr
  let modusTollens ← mkAppM ``mt #[deMorgan]
  let notNotHyp ← mkAppM ``notNotIntro #[withoutFalse]
  let answer := mkApp modusTollens notNotHyp
  return answer

syntax (name := liftOrNToNeg) "liftOrNToNeg" term : tactic

@[tactic liftOrNToNeg] def evalLiftOrNToNeg : Tactic :=
  fun stx => withMainContext do
    trace[smt.profile] m!"[liftOrNToNeg] start time: {← IO.monoNanosNow}ns"
    let hyp ← elabTerm stx[1] none
    let answer ← liftOrNToNegMeta hyp
    let mvar ← getMainGoal
    let type ← Meta.inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile] m!"[liftOrNToNeg] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying
