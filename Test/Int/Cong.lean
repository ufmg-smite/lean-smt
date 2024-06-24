import Smt

theorem cong (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  smt
