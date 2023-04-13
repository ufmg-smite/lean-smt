import Smt

open Smt.Reconstruction.Certifying

example {a b c : Int} : a < b → 0 < c → c * a < c * b := by
  intros h₁ h₂
  arithMulPos h₁, h₂

example {a b c : ℚ} : a ≤ b → 0 > c → c * a ≥ c * b := by
  intros h₁ h₂
  arithMulNeg h₁, h₂
