import Smt

theorem addition (p q : Prop) : p → p ∨ q := by
  smt
  simp_all
