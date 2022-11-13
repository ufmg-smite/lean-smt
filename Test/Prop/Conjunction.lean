import Smt

theorem conjunction (p q : Prop) : p → q → p ∧ q := by
  smt
