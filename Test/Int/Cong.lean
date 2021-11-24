import Smt

theorem cong (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  smt
  simp_all
