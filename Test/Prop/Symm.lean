import Smt

example (p q : Prop) : p = q → q = p := by
  smt
