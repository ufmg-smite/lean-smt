import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Order


theorem unwrapDecide {p : Prop} [inst : Decidable p] : decide p = true → p := by
  intros h
  unfold decide at h
  cases inst with
  | isFalse _ => simp at h
  | isTrue h' => exact h'

theorem wrapDecide {p : Prop} [inst : Decidable p] : ¬ p → decide p = false := by
  intros h
  unfold decide
  cases inst with
  | isFalse _ => simp
  | isTrue hp => exact absurd hp h

theorem castLE : ∀ {a b : Int}, a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by
  intros a b h
  have bNumerator: (Rat.ofInt b).num = b := Rat.ofInt_num
  show Rat.blt b a = false
  unfold Rat.blt
  split_ifs with h₁ h₂ h₃
  { 
    simp at h₁
    have ⟨h₁f, h₁s⟩ := h₁
    have bNeg : b < 0 := unwrapDecide h₁f
    have aNotNeg : 0 ≤ a := unwrapDecide h₁s
    have abs : b < a := lt_of_lt_of_le bNeg aNotNeg
    exact (not_le_of_gt abs) h
  }
  {
    have h₂' := symm h₂
    have bEq0 : 0 = b := Eq.trans h₂' bNumerator
    rw [← bEq0] at h
    simp
    have abs := not_lt_of_ge h
    exact wrapDecide abs
  }
  { exact rfl }
  simp
  exact h

theorem floorLtImplies : ∀ {c : Rat} {i : Int}, Rat.floor c < i → Rat.floor c + 1 ≤ i := sorry

theorem floorPlusOneGt : ∀ (c : Rat), c < Rat.ofInt (Rat.floor c + 1) := sorry

theorem intTightUb : ∀ {i : Int} {c : Rat}, i < c → i ≤ Rat.floor c := by
  intros i c h
  cases lt_trichotomy i (Rat.floor c) with
  | inl iltc => exact le_of_lt iltc
  | inr h'   => cases h' with
                | inl ieqc => exact le_of_eq ieqc
                | inr igtc =>
                  have bloh := castLE (floorLtImplies igtc)
                  have bluh := floorPlusOneGt c
                  have h' := lt_of_lt_of_le bluh bloh
                  exact absurd h (lt_asymm h')

theorem intTightLb : ∀ {i : Int} {c : Rat}, i > c → i ≥ Rat.ceil c := sorry
