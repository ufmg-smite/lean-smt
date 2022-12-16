import Std.Data.Rat.Basic

#check Rat

theorem Rat.add_lt_add_left {a b : Rat} (h : a < b) (c : Rat) : c + a < c + b := by
  admit

theorem sumBounds₁ : ∀ {p q r s : Rat}, p < q → r < s → p + r < q + s := by
  intros p q r s h₁ h₂

  admit

