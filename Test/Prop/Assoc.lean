import Smt

theorem assoc (f : Prop → Prop → Prop) (p q r : Prop) :
  f p (f q r) = f (f p q) r := by
  smt
  admit
