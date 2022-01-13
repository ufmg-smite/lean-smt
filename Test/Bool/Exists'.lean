import Smt

theorem exists' : ∃ (p : Bool), true := by
  smt
  exact Exists.intro true rfl
