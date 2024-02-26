import Smt

example (p q : Prop) (f : Prop → Prop) : p = q → f p = f q := by
  smt
