import Smt

theorem simplification (p q : Prop) : p ∧ q → p := by
  smt
  simp_all
