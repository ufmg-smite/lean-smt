import Smt

theorem symm (p q : Prop) : p = q → q = p := by
  smt
  simp_all
