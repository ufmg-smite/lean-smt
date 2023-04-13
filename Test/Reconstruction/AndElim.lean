import Smt

open Smt.Reconstruction.Certifying

example : A ∧ B ∧ C ∧ D → B := by
  intro h
  andElim h, 1
