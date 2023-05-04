import Smt

open Smt.Reconstruction.Certifying

example : ¬ (A ∨ B ∨ C ∨ D) → ¬ C := by
  intro h
  notOrElim h, 2
