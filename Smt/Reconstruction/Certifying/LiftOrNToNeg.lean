import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

syntax (name := liftOrNToNeg) "liftOrNToNeg" term : tactic

@[tactic liftOrNToNeg] def evalLiftOrNToNeg : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let hypType ← inferType hyp
    let props := map notExpr (collectPropsInOrChain hypType)
    let propsList: Expr := listExpr props $ Expr.sort Level.zero
    let deMorgan: Expr := mkApp (mkConst `deMorgan₂) propsList
    let modusTollens: Expr ← mkAppM `modusTollens #[deMorgan]
    let notNotHyp: Expr ← mkAppM `notNotIntro #[hyp]
    let answer := mkApp modusTollens notNotHyp
    Tactic.closeMainGoal answer

theorem modusTollens {A B : Prop} : (A → B) → ¬ B → ¬ A := by
  intros f nb
  exact match Classical.em A with
  | Or.inl ha  => absurd (f ha) nb
  | Or.inr hna => hna

example : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D → ¬ (A ∧ B ∧ C ∧ D) := by
  intro h
  liftOrNToNeg h
--  fun h => modusTollens (@deMorgan₂ [A, B, C, D]) (notNotIntro h)

