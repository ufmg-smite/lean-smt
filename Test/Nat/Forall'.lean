import Smt

theorem forall' : ∀ x : Nat, x ≥ 0 := by
  smt
  simp [Nat.zero_le]
