import Smt

open Smt.Reconstruction.Certifying

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ C ∨ D ∨ B ∨ E := by
  intro h
  permutateOr h, [0, 2, 3, 1, 4]

example : A ∨ (B ∨ C) ∨ (D ∨ E ∨ F) → (D ∨ E ∨ F) ∨ A ∨ (B ∨ C) := by
  intro h
  permutateOr h, [2, 0, 1], 2

