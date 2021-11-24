import Smt

theorem falsum : !false := by
  smt
  simp_all
