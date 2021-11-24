import Smt

theorem resolution (p q r : Prop) : p ∨ q → ¬p ∨ r → q ∨ r := by
  smt
  intro hpq
  intro hnpr
  induction hpq <;> simp_all
