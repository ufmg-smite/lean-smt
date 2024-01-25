import Smt

theorem cong (x y : Nat) (f : Nat → Nat) : x = y → f x = f y := by
  smt_show
  simp_all
