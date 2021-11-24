import Smt

theorem trans (p q r : Prop) : p = q → q = r → p = r := by
  smt
  simp_all
