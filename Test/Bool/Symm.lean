import Smt

example (p q : Bool) : p == q → q == p := by
  smt
  cases p <;> cases q <;> simp_all
