import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.LiftOrNToImp
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

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

def removeFalseCore (hyp hypType : Expr) (stx : Syntax) (out : Name) : TacticM Unit := do
  let length := getLength hypType
  let fid: TacticM Ident := do
    if length > 2 then
      let fname ← mkFreshId
      groupOrPrefixCore hyp hypType (length - 1) fname
      return (mkIdent fname)
    else return (mkIdent stx[1].getId)
  let fid ← fid
  evalTactic (← `(tactic| have $(mkIdent out) := orFalse $fid))

@[tactic removeFalse] def evalRemoveFalse : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let hypType ← inferType hyp
    let out: Ident := ⟨stx[3]⟩
    removeFalseCore hyp hypType stx out.getId

example : ¬ A ∨ ¬ B ∨ ¬ C ∨ False → ¬ A ∨ ¬ B ∨ ¬ C := by
  intro h
  removeFalse h, h₁
  exact h₁

syntax (name := liftOrNToNeg) "liftOrNToNeg" term : tactic

@[tactic liftOrNToNeg] def evalLiftOrNToNeg : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let hypType ← inferType hyp
    let fname ← mkFreshId
    removeFalseCore hyp hypType stx fname
    withMainContext do
      let lctx ← getLCtx
      let hyp' := (lctx.findFromUserName? fname).get!.toExpr
      let hypType' ← instantiateMVars (← inferType hyp')
      let props := map notExpr (collectPropsInOrChain hypType')
      let propsList: Expr := listExpr props $ Expr.sort Level.zero
      let deMorgan: Expr := mkApp (mkConst `deMorgan₂) propsList
      let modusTollens: Expr ← mkAppM `modusTollens #[deMorgan]
      let notNotHyp: Expr ← mkAppM `notNotIntro #[hyp']
      let answer := mkApp modusTollens notNotHyp
      Tactic.closeMainGoal answer

theorem modusTollens {A B : Prop} : (A → B) → ¬ B → ¬ A := by
  intros f nb
  exact match Classical.em A with
  | Or.inl ha  => absurd (f ha) nb
  | Or.inr hna => hna

example : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D ∨ False → ¬ (A ∧ B ∧ C ∧ D) := by
  intro h
  liftOrNToNeg h

