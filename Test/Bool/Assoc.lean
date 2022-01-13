import Smt

theorem assoc (f : Bool → Bool → Bool) (p q r : Bool) :
  f p (f q r) == f (f p q) r := by
  smt
  admit
