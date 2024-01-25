import Smt

theorem modus_ponens (p q : Bool) : p → (p → q) → q := by
  smt_show
  simp_all
