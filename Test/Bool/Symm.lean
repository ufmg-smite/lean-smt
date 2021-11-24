import Smt

theorem symm (p q : Bool) : p = q → q = p := by
  smt
  simp_all
