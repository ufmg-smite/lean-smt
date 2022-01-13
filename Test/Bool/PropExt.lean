import Smt

theorem prop_ext (p q : Bool) : (p ↔ q) → p == q := by
  smt
  intro hpq
  cases hpq <;> cases p <;> cases q <;> simp_all
