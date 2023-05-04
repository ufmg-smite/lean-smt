import Smt

example (p : Bool) : p == p := by
  smt
  cases p <;> simp_all
