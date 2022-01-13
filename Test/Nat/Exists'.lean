import Smt

theorem exists' : ∃ x : Int, x = 1 := by
  smt
  exact ⟨1, rfl⟩
