import Smt

theorem conjunction (p q : Bool) : p → q → p && q := by
  smt
  simp_all
