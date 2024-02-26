import Smt

open Smt.Reconstruct

example : A ∧ B ∧ C ∧ D → B := by
  intro h
  andElim h, 1
