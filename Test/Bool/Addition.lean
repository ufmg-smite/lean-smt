import Smt

theorem addition (p q : Bool) : p → p || q := by
  smt_show
  simp_all
