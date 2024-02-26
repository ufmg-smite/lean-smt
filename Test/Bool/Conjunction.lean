import Smt

theorem conjunction (p q : Bool) : p → q → p && q := by
  smt_show
  simp_all
