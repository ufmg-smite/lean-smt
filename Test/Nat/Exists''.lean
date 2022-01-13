import Smt

theorem exists'' : ∃ x : Nat, x ≥ 0 := by
  smt
  exact ⟨0, by decide⟩
