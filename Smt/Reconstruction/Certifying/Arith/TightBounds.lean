import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor

theorem Rat.neg_lt_neg {a b : ℚ} (h : a < b) : -a > -b := by
  simp
  exact h

theorem castLE : ∀ {a b : Int}, a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by simp

theorem floorPlusOneGt : ∀ (c : Rat), c < Rat.ofInt (⌊c⌋ + 1) := by
  intro c
  have uncasted_pf := Int.lt_floor_add_one c
  norm_cast at uncasted_pf

theorem intTightUb : ∀ {i : Int} {c : Rat}, Rat.ofInt i < c → i ≤ ⌊c⌋ := by
  intros i c h
  cases lt_trichotomy i (Rat.floor c) with
  | inl iltc => exact le_of_lt iltc
  | inr h'   => cases h' with
                | inl ieqc => exact le_of_eq ieqc
                | inr igtc =>
                  have floor_le_i := (Int.lt_iff_add_one_le ⌊c⌋ i).mp igtc
                  have coe_igtc := castLE floor_le_i
                  have c_lt := floorPlusOneGt c
                  have h' := lt_of_lt_of_le c_lt coe_igtc
                  exact absurd h (lt_asymm h')

theorem intTightLb : ∀ {i : Int} {c : ℚ}, i > c → i ≥ ⌈c⌉ := by
  intros i c h
  have neg_c_lt_neg_i := Rat.neg_lt_neg h
  have i_le_floor_neg_c := intTightUb neg_c_lt_neg_i
  have neg_floor_neg_c_le_neg_i := Int.neg_le_neg i_le_floor_neg_c
  simp at neg_floor_neg_c_le_neg_i
  rw [Int.floor_neg] at neg_floor_neg_c_le_neg_i
  simp at neg_floor_neg_c_le_neg_i
  exact neg_floor_neg_c_le_neg_i
