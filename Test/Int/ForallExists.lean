import Smt

theorem forallExists : ∀ x : Nat, ∃ y : Int, x ≤ y := by
  smt
