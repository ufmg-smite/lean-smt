import Smt

theorem prop_ext (p q : Prop) : (p ↔ q) → p = q := by
  smt
  simp_all
