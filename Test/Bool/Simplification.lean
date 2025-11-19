import Smt

theorem simplification (p q : Bool) : p && q → p := by
  smt
