import Smt

open Smt.Reconstruct

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ C ∨ D ∨ B ∨ E := by
  intro h
  permutateOr h, [0, 2, 3, 1, 4]

example : A ∨ B ∨ C ∨ (D ∨ E ∨ F) → (D ∨ E ∨ F) ∨ B ∨ C ∨ A := by
  intro h
  permutateOr h, [3, 1, 2, 0], 3

example : (D ∨ E ∨ F ∨ G) ∨ (K ∨ I) ∨ (A ∨ B ∨ C) → (A ∨ B ∨ C) ∨ (K ∨ I) ∨ (D ∨ E ∨ F ∨ G) := by
  intro h
  permutateOr h, [2, 1, 0], 2

example : (D ∨ E ∨ F ∨ G) ∨  (A ∨ B ∨ C ∨ Z ∨ W ∨ J ∨ L) ∨ (K ∨ I) → (A ∨ B ∨ C ∨ Z ∨ W ∨ J ∨ L) ∨ (K ∨ I) ∨ (D ∨ E ∨ F ∨ G) := by
  intro h
  permutateOr h, [1, 2, 0], 2
