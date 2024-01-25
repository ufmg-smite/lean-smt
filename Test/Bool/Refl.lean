import Smt

example (p : Bool) : p == p := by
  smt_show
  cases p <;> simp_all
