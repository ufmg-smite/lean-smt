import Smt

theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  smt
  simp_all
