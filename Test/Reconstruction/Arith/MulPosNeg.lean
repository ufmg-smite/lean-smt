import Smt

open Smt.Reconstruction.Certifying

example {a b c : Int} : a < b → 0 < c → c * a < c * b := by
  arithMulPos [a,b,c], 0

example {a b c : ℚ} : a ≤ b → 0 > c → c * a ≥ c * b := by
  arithMulNeg [a,b,c], 1

