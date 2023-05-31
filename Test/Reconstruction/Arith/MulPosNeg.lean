import Smt

open Smt.Reconstruction.Certifying

example {a b c : Int} : a < b → c > 0 → c * a < c * b := by
  arithMulPos [a,b,c], 0

example {a b c : ℚ} : a ≤ b → 0 > c → c * a ≥ c * b := by
  arithMulNeg [a,b,c], 1

example {a b c : Int} : a < b → 0 < 2 * c → (2 * c) * a < (2 * c) * b := by
  arithMulPos [a, b, 2 * c], 0

example {a b : Int} : a < b → 0 < (2 : Int) → 2 * a < 2 * b := by
  arithMulPos [a,b,2], 0
