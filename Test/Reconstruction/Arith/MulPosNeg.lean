import Smt

open Smt.Reconstruction.Certifying

example {a b c : Int} : c > 0 ∧ a < b → c * a < c * b := by
  arithMulPos [a,b,c], 0

example {a b c : Real} : 0 > c ∧ a ≤ b → c * a ≥ c * b := by
  arithMulNeg [a,b,c], 1

example {a b c : Int} : 0 < 2 * c ∧ a < b → (2 * c) * a < (2 * c) * b := by
  arithMulPos [a, b, 2 * c], 0

/- example {a b : Int} : 0 < (2 : Int) ∧ a < b → 2 * a < 2 * b := by -/
/-   arithMulPos [a,b,2], 0 -/

example {a b c : Int} : 0 < 2 * c ∧ a < b → (2 * c) * a < (2 * c) * b := by
  arithMulPos [a, b, 2 * c], 0

example {a b c : Int} : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b c : Real}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b : Real} {c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b : Real} {c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a c : Real} {b : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a : Real} {b c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {b c : Real} {a : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {b : Real} {a c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {c : Real} {a b : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

