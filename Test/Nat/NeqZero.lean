import Smt

theorem neq_zero : ∀ (x : Nat), x ≠ 0 := by
  smt_show
  admit

theorem succ_neq_zero : ∀ (x : Nat), x + 1 ≠ 0 := by
  smt_show
  admit
