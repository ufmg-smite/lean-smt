import Smt

theorem comm (f : Prop → Prop → Prop) (p q : Prop) : f p q = f q p := by
  smt
  admit
