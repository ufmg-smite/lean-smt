import Smt

example (p q r : Prop) : p = q → q = r → p = r := by
  smt
