import Smt

open Smt.Reconstruction.Certifying

example : A ∨ B ∨ C ∨ B → A ∨ B ∨ C := by
  intro h
  factor h

example : A ∨ B ∨ B → A ∨ B := by
  intro h
  factor h

example : A ∨ A ∨ A ∨ A ∨ B ∨ A ∨ B ∨ A ∨ C ∨ B ∨ C ∨ B ∨ A → A ∨ B ∨ C :=
  by intro h
     factor h

example : (A ∨ B) ∨ C ∨ D ∨ C ∨ (A ∨ B) → (A ∨ B) ∨ C ∨ D := by
  intro h
  factor h, 4

example : (A ∨ B ∨ C) ∨ (A ∨ B ∨ C) → A ∨ B ∨ C := by
  intro h
  factor h, 1

example :
  A ∨ B ∨ (E ∨ F) ∨ A ∨ B ∨ (E ∨ F) → A ∨ B ∨ (E ∨ F) :=
  by intro h
     factor h, 5
