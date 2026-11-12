import Smt
import Smt.Real

-- `ARITH_REDUCTION` of `div_total` / `mod_total`: no goal is left over.

example : ∀ x : Int, x % 2 = 0 → ¬ x ≤ 1 → x / 2 < x := by
  smt

example : ∀ x : Int, ¬ x ≤ 1 → 0 ≤ x / 2 := by
  smt

example (x : Int) : x % 3 < 3 := by
  smt

example (x : Int) : x / (-3) * (-3) ≤ x := by
  smt

example (x : Int) : x % (-3) ≥ 0 := by
  smt

-- The partial `div` / `mod` with a divisor that may be zero.

example (n m : Int) (h : 0 < m) : n % m < m := by
  smt [h]

example (n m : Int) (h : m < 0) : m * (n / m) ≤ n := by
  smt [h]

example (n m : Int) : n = m * (n / m) + n % m ∨ m = 0 := by
  smt
