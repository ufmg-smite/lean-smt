import Smt

open Smt.Reconstruction.Certifying

example {a b c d e f : Nat} : a < d → b < e → c < f → a + (b + c) < d + (e + f) := by
  intros h₁ h₂ h₃
  sumBounds [h₁, h₂, h₃]

example {a b c d e f w z : Int} :
  a ≤ d → b ≤ e → c ≤ f → w ≤ z → a + (b + (c + w)) ≤ d + (e + (f + z)) := by
    intros h₁ h₂ h₃ h₄
    sumBounds [h₁, h₂, h₃, h₄]

example {a b c d e f : ℚ} : a < d → b ≤ e → c ≤ f → a + (b + c) < d + (e + f) := by
  intros h₁ h₂ h₃
  sumBounds [h₁, h₂, h₃]

example {a b c d e f : Nat} : a < d → b < e → c < f → a + (b + c) < d + (e + f) := by
  intros h₁ h₂ h₃
  sumBounds [h₁, h₂, h₃]

