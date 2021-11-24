import Smt

theorem cong (x y : Nat) (f : Nat → Nat) : x = y → f x = f y := by
  smt
  simp_all
