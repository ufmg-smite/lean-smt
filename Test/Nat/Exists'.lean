import Smt

theorem exists' : ∃ x : Nat, x = 1 := by
  smt_show
  exact ⟨1, rfl⟩
