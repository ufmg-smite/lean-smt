import Smt

variable (f : Int → Int)

example (h : f 10 = 10) : let y := 10; f y = 10 := by
  smt [h]
  exact h

example (h : let y := 10; f y = 10) : f 10 = 10 := by
  smt [h]
  exact h

-- example (h : f 10 = 10) : f 10 = 10 := by
--   let z : Int := 10
--   have : 10 = z := rfl
--   rw [this]
--   smt [h, z]
--   exact h
