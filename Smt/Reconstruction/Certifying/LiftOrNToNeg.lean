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

namespace Smt.Reconstruction.Certifying.LiftOrNToNeg

open Boolean LiftOrNToImp Util

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

def removeFalseCore (mvar : MVarId) (val type : Expr) (name : Name)
  : MetaM MVarId := mvar.withContext do
  let length := getLength type
  let props := collectPropsInOrChain type
  let goal := createOrChain $ List.dropLast props
  if length > 2 then
    let fname ← mkFreshId
    let mvar' ← groupPrefixCore mvar val type (length - 1) fname
    mvar'.withContext do
      let lctx ← getLCtx
      let groupped := (lctx.findFromUserName? fname).get!.toExpr
      let answer ← mkAppM ``orFalse #[groupped]
      let (_, mvar'') ← MVarId.intro1P $ ← mvar'.assert name goal answer
      return mvar''
  else
    let answer ← mkAppM ``orFalse #[val]
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal answer
    return mvar'


@[tactic removeFalse] def evalRemoveFalse : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let hypType ← inferType hyp
    let out: Ident := ⟨stx[3]⟩
    let mvar ← getMainGoal
    let mvar' ← removeFalseCore mvar hyp hypType out.getId
    replaceMainGoal [mvar']

example : ¬ A ∨ B ∨ ¬ C ∨ False → ¬ A ∨ B ∨ ¬ C := by
  intro h
  removeFalse h, h₁
  exact h₁

def liftOrNToNegMeta (mvar : MVarId) (val : Expr) (name : Name)
  : MetaM MVarId := mvar.withContext do
  let type ← inferType val
  let fname ← mkFreshId
  let mvar' ← removeFalseCore mvar val type fname
  mvar'.withContext do
    let lctx ← getLCtx
    let withoutFalse := (lctx.findFromUserName? fname).get!.toExpr
    let type' ← instantiateMVars (← inferType withoutFalse)
    let propsList := collectPropsInOrChain type'
    let notPropsList := map notExpr propsList
    let propsListExpr := listExpr notPropsList $ Expr.sort Level.zero
    let deMorgan := mkApp (mkConst ``deMorgan₂) propsListExpr
    let modusTollens ← mkAppM ``mt #[deMorgan]
    let notNotHyp ← mkAppM ``notNotIntro #[withoutFalse]
    let goal := mkApp (mkConst ``Not) (foldAndExpr notPropsList)
    let answer := mkApp modusTollens notNotHyp
    let (_, mvar'') ← MVarId.intro1P $ ← mvar'.assert name goal answer
    return mvar''

syntax (name := liftOrNToNeg) "liftOrNToNeg" term "," term : tactic

@[tactic liftOrNToNeg] def evalLiftOrNToNeg : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let name := stx[3].getId
    let mvar ← getMainGoal
    let mvar' ← liftOrNToNegMeta mvar hyp name
    replaceMainGoal [mvar']

example : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D ∨ False → ¬ (A ∧ B ∧ C ∧ D) := by
  intro h
  liftOrNToNeg h, h₂
  exact h₂

end Smt.Reconstruction.Certifying.LiftOrNToNeg
