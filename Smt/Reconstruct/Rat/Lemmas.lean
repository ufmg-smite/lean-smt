/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

import Batteries.Data.Int
import Batteries.Data.Rat

import Smt.Reconstruct.Int.Core
import Smt.Reconstruct.Rat.Core



namespace Rat



section le_lt_defs

variable {x y : Rat}

protected theorem le_antisymm (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
    rw [Rat.le_iff_sub_nonneg] at hxy hyx
    rw [Rat.sub_eq_add_neg] at hyx
    rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hxy
    have this := Rat.eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hyx hxy)
    rwa [Rat.neg_neg] at this

protected theorem le_def : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := by
  rw [← num_divInt_den y, ← num_divInt_den x]
  conv => rhs ; simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast x.den_pos) (mod_cast y.den_pos)


protected theorem le_total : x ≤ y ∨ y ≤ x := by
  simp [Rat.le_def]
  omega

protected theorem lt_iff_le_not_le : x < y ↔ (x ≤ y ∧ ¬ y ≤ x) := by
  rw [← Rat.not_le, and_iff_right_of_imp Rat.le_total.resolve_left]

protected theorem lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y := ⟨
  fun h => ⟨Rat.le_of_lt h, Rat.ne_of_lt h⟩,
  fun h => by
    let ⟨h_le, h_ne⟩ := h
    rw [Rat.lt_iff_le_not_le]
    apply And.intro h_le
    intro h_le'
    let _ := Rat.le_antisymm h_le h_le'
    contradiction
⟩

protected theorem lt_def : x < y ↔ x.num * y.den < y.num * x.den := by
  rw [Rat.lt_iff_le_and_ne, Rat.le_def]
  suffices x ≠ y ↔ x.num * y.den ≠ y.num * x.den by
    constructor <;> intro h
    · exact Int.lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := Int.lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact Decidable.not_iff_not.mpr Rat.eq_iff_mul_eq_mul

end le_lt_defs

end Rat



private theorem Rat.mul_lt_mul_left {c x y : Rat} : 0 < c → ((c * x < c * y) ↔ (x < y)) :=
  numDenCasesOn' x fun nx dx nz_dx =>
    numDenCasesOn' y fun ny dy nz_dy =>
      numDenCasesOn' c fun nc dc nz_dc => by
        sorry

private theorem Rat.mul_le_mul_left {c x y : Rat} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  sorry

private theorem Rat.mul_eq_zero_left {x y : Rat} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  sorry

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Rat

variable {a b c d : Rat}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  sorry

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  sorry

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  sorry

theorem neg_lt_neg (h : a < b) : -a > -b := by
  sorry

theorem neg_le_neg (h : a ≤ b) : -a ≥ -b := by
  sorry

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.floor := by
  sorry

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.ceil := by
  sorry

theorem trichotomy₁ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  sorry

theorem trichotomy₂ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  sorry

theorem trichotomy₃ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  sorry

theorem trichotomy₄ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  sorry

theorem trichotomy₅ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  sorry

theorem trichotomy₆ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  sorry

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  sorry

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  sorry

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  sorry

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  sorry

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  sorry

theorem lt_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) = 0) = (x - y = 0) := by
    apply propext; constructor
    · apply Rat.mul_eq_zero_left sorry
    · intro hxy; rw [hxy, Rat.mul_zero]
  rw [@eq_eq_sub_eq_zero a₁, @eq_eq_sub_eq_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  sorry

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  sorry

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  sorry

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  sorry

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  sorry

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  sorry

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  sorry

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  sorry

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  sorry

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  sorry

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  sorry

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  sorry

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  sorry

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat
