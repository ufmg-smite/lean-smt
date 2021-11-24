import Smt

theorem addition (p q : Bool) : p → p || q := by
  smt
  simp_all
