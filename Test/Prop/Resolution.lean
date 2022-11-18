import Smt

theorem resolution (p q r : Prop) : p ∨ q → ¬p ∨ r → q ∨ r := by
  smt
