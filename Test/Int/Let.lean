import Smt

variable (f : Int → Int)

example (h : f 10 = 10) : let y := 10; f y = 10 := by
  smt [h]

example (h : let y := 10; f y = 10) : f 10 = 10 := by
  smt [h]

example (h : f 10 = 10) : f 10 = 10 := by
  let z : Int := 10
  have : 10 = z := rfl
  rw [this]
  smt_show [h, z]
  exact h

example (h : f 10 = 10) : f 10 = 10 := by
  let z : Int := 10
  let y : Int := z
  have : 10 = y := rfl
  rw [this]
  smt_show [h, y, z]
  exact h

example (h : f 10 = 10) : f 10 = 10 := by
  let z (_ : Int) : Int := f 10
  have : f 10 = z 3 := rfl
  rw [this]
  smt_show [h, z]
  exact h
