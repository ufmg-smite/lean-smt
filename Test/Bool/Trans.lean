import Smt

theorem trans (p q r : Bool) : p == q → q == r → p == r := by
  smt
  cases p <;> cases q <;> cases r <;> simp_all
