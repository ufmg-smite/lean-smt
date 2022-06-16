import Smt

theorem exists' : ∃ x : Nat, x = 1 := by
  smt
  exact ⟨1, rfl⟩
