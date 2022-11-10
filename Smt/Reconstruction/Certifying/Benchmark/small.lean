import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Resolution
import Smt.Reconstruction.Certifying.Factor
import Smt.Reconstruction.Certifying.PermutateOr

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

example : ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ A → A ∨ ¬ (A ∧ B) → ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ (A ∧ B) := by
  intros h₁ h₂
  R2 h₁, h₂, A

example : A ∧ B ∧ C ∧ D ∧ E → D := by
  intro h
  andElim h, 3

example : ¬ (A ∨ B ∨ C ∨ D) → ¬ C := by
  intro h
  notOrElim h, 2
