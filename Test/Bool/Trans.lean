import Smt

example (p q r : Bool) : p == q → q == r → p == r := by
  smt
