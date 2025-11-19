import Smt

theorem cong (p q : Bool) (f : Bool → Bool) : p == q → f p == f q := by
  smt
