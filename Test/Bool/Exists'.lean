import Smt

theorem exists' : ∃ p : Bool, p := by
  smt
  exact Exists.intro true rfl
