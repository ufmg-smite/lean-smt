import Smt

theorem exists' : ∃ p : Prop, p := by
  smt
  exact Exists.intro True True.intro
