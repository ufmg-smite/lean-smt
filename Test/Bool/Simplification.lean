import Smt

theorem simplification (p q : Bool) : p && q → p := by
  smt
  cases p <;> simp_all
