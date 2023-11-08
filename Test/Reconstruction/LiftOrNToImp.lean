import Smt

open Smt.Reconstruction.Certifying

example : ¬ A ∨ ¬ B ∨ C ∨ D ∨ E → A ∧ B → C ∨ D ∨ E  := by
  intro h
  liftOrNToImp h, 2

example : ¬ A ∨ ¬ B ∨ C ∨ D ∨ E → ((A ∧ B) → C ∨ D ∨ E) := fun h => by
  liftOrNToImp h, 2

example :
  let p1 := ¬ A ∨ ¬ B ∨ C ∨ D ∨ E
  let p2 := ((A ∧ B) → C ∨ D ∨ E)
  p1 → p2 := fun h => by
  liftOrNToImp h, 2
