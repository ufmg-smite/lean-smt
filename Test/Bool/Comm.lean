import Smt

theorem comm (f : Bool → Bool → Bool) (p q : Bool) : f p q == f q p := by
  smt
  admit
