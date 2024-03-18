import Smt

theorem exists' : ∃ p : Bool, p := by
  smt_show
  exact Exists.intro true rfl
