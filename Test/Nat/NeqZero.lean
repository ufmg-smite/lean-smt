import Smt

theorem neq_zero : ∀ (x : Nat), x ≠ 0 := by
  intro x
  smt +model

theorem succ_neq_zero : ∀ (x : Nat), x + 1 ≠ 0 := by
  smt
