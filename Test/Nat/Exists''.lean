import Smt

theorem exists'' : ∃ x : Nat, x ≥ 0 := by
  smt_show
  exact ⟨0, by decide⟩
