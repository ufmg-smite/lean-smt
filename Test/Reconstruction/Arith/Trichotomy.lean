import Smt

open Smt.Reconstruct

example {a b : Nat} : a ≥ b → ¬ a = b → a > b := by
  intros h₁ h₂
  trichotomy h₁, h₂
