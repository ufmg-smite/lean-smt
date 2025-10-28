import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

open Real

theorem Rat.cast_eq (x y : Rat) : (x = y) = ((x : Real) = (y : Real)) := by
  simp only [Rat.cast_inj]

theorem Rat.cast_ge (x y : Rat) : (x ≥ y) = ((x : Real) ≥ (y : Real)) := by
  simp only [ge_iff_le, Rat.cast_le]

theorem Rat.cast_gt (x y : Rat) : (x > y) = ((x : Real) > (y : Real)) := by
  simp only [gt_iff_lt, Rat.cast_lt]

theorem Rat.cast_ne (x y : Rat) : x ≠ y ↔ (x : Real) ≠ (y : Real) := by
  simp only [ne_eq, Rat.cast_inj]

theorem Rat.cast_eq_div_int (q : Rat) : ∃ (a b : Int), (q : Real) = (a : Real) / b := by
  use q.num
  use q.den
  rw [@Int.cast_natCast, ← @Rat.cast_def]
