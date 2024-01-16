import Smt

open Smt.Reconstruct

example : ¬ (A ∨ B ∨ C ∨ D) → ¬ C := by
  intro h
  notOrElim h, 2
