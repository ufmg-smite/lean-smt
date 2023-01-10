import Smt.Reconstruction.Certifying.Arith

#check sumBounds₁

example : ∀ {a b c d : Rat}, a < b → c < d → a + c < b + d := by
  intros a b c d h₁ h₂
  sumBounds h₁, h₂
