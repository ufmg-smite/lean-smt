import Smt

theorem forall' : ∀ x : Nat, x ≥ 0 := by
  smt_show
  simp [Nat.zero_le]
