import Smt

theorem cong (p q : Prop) (f : Prop → Prop) : p = q → f p = f q := by
  smt
  simp_all
