import Smt

example (p q : Bool) : p == q → q == p := by
  smt_show
  cases p <;> cases q <;> simp_all
