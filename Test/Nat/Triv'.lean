import Smt

theorem triv' : 0 + 1 = 1 := by
  smt_show
  simp_all
