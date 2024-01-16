import Smt

open Smt.Reconstruct

example : ¬ A ∨ B ∨ ¬ C ∨ False → ¬ A ∨ B ∨ ¬ C := by
  intro h
  removeFalse h, h₁
  exact h₁

example : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D ∨ False → ¬ (A ∧ B ∧ C ∧ D) := by
  intro h
  liftOrNToNeg h
