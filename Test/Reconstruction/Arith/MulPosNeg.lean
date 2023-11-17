import Smt

open Smt.Reconstruction.Certifying

example {a b c : Int} : c > 0 ∧ a < b → c * a < c * b := by
  arithMulPos [a,b,c], 0

example {a b c : ℚ} : 0 > c ∧ a ≤ b → c * a ≥ c * b := by
  arithMulNeg [a,b,c], 1

example {a b c : Int} : 0 < 2 * c ∧ a < b → (2 * c) * a < (2 * c) * b := by
  arithMulPos [a, b, 2 * c], 0

example {a b : Int} : 0 < (2 : Int) ∧ a < b → 2 * a < 2 * b := by
  arithMulPos [a,b,2], 0

example {a b c : Int} : 0 < 2 * c ∧ a < b → (2 * c) * a < (2 * c) * b := by
  arithMulPos [a, b, 2 * c], 0

example {a b c : Int} : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b c : Rat}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b : Rat} {c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b : Rat} {c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a c : Rat} {b : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a : Rat} {b c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {b c : Rat} {a : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {b : Rat} {a c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {c : Rat} {a b : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

example {a b c : Int}  : 0 < c ∧ a < b → c * a < c * b := by
  arithMulPos [a, b, c], 0

