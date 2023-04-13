import Smt

open Smt.Reconstruction.Certifying

example : ¬ A ∨ ¬ B ∨ C ∨ D ∨ E → A ∧ B → C ∨ D ∨ E  := by
  intro h
  liftOrNToImp h, 2
