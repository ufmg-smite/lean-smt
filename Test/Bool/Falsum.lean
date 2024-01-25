import Smt

theorem falsum : !false := by
  smt_show
  simp_all
