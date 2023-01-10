import Smt.Reconstruction.Certifying.Arith

#check sumBounds₁
#check trichotomy₁

example : ∀ {a b c d : Rat}, a < b → c < d → a + c < b + d := by
  intros a b c d h₁ h₂
  sumBounds h₁, h₂

example : ∀ {a b : Int}, (¬ (a = b)) ∧ (¬ (a > b)) → a < b := by
  intros a b h
  have ⟨h₁, h₂⟩ := h
  trichotomy h₁, h₂
