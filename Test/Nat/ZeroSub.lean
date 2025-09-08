import Smt

example : 0 - x = 0 := by
  smt_show
  induction x <;> simp_all
