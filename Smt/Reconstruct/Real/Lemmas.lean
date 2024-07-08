/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Archimedean

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Real

variable {a b c d : Real}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := add_lt_add_left h₂ a
  have r₂ : a + d < b + d := add_lt_add_right h₁ d
  exact lt_trans r₁ r₂

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have r₁ : a + c ≤ a + d := add_le_add_left h₂ a
  have r₂ : a + d < b + d := add_lt_add_right h₁ d
  exact lt_of_le_of_lt r₁ r₂

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  exact add_lt_add_right h₁ d

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := add_le_add_right h₁ d
  exact lt_of_lt_of_le r₁ r₂

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have r₁ : a + c ≤ a + d := add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := add_le_add_right h₁ d
  exact le_trans r₁ r₂

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂]
  exact add_le_add_right h₁ d

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁]
  exact add_lt_add_left h₂ b

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact add_le_add_left h₂ b

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₁, h₂]
  exact le_refl (b + d)

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ ⌊c⌋ :=
  Int.le_floor.mpr (le_of_lt h)

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ ⌈c⌉ :=
  Int.ceil_le.mpr (le_of_lt h)

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (not_lt.mpr h₁)) h₂

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (not_lt.mpr h₂)) (not_lt.mpr h₁)

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (not_lt.mpr h₂)) h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (not_lt.mpr h₂)) h₁

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (not_lt.mpr h₁)) (not_lt.mpr h₂)

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  have tr := lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (not_lt.mpr h₁)) h₂

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply sub_neg_of_lt
  · apply lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact sub_nonpos_of_le
  · exact le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact sub_nonneg_of_le
  · exact le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact sub_pos_of_lt
  · exact lt_of_sub_pos

theorem lt_of_sub_eq {c₁ c₂ : Real} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Real} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq {c₁ c₂ : Real} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Real} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem eq_of_sub_eq {c₁ c₂ : Real} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  have {c x y : Real} (hc : c > 0) : (c * (x - y) = 0) = (x - y = 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_right_inj' (ne_of_gt hc)]
  rw [@eq_eq_sub_eq_zero a₁, @eq_eq_sub_eq_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq {c₁ c₂ : Real} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Real} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, ge_iff_le, mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq {c₁ c₂ : Real} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Real} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, gt_iff_lt, mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  have h := mul_lt_mul_of_neg_right ha hb
  simp at h
  exact h

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  have h := mul_lt_mul_of_pos_right ha hb
  simp at h
  exact h

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  have h := mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  have h := mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  match lt_trichotomy a 0 with
  | .inl hn         => mul_sign₁ hn hn
  | .inr (.inl hz)  => absurd hz ha
  | .inr (.inr hp)  => mul_sign₆ hp hp

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  match lt_trichotomy b 0 with
  | .inl hn         => mul_sign₄ (mul_sign₁ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₃ (mul_sign₃ ha hp) hp

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  match lt_trichotomy b 0 with
  | .inl hn         => mul_sign₁ (mul_sign₄ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₆ (mul_sign₆ ha hp) hp

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h.2 (le_of_lt h.1)

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  mul_le_mul_of_nonpos_left h.2 (le_of_lt h.1)

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b := by
  match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
  | Or.inl xaNeg,           Or.inl ybNeg           =>
    nlinarith
  | Or.inl xaNeg,           Or.inr (Or.inl ybZero) =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaNeg' ybZero')
  | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inl (And.intro xaNeg' ybPos')
  | Or.inr (Or.inl xaZero), Or.inl ybNeg           =>
    have xaZero' := ge_of_eq xaZero
    simp at xaZero'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inr (And.intro xaZero' ybNeg')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaZero' ybZero')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inl (And.intro xaZero' ybPos')
  | Or.inr (Or.inr xaPos),  Or.inl ybNeg           =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inr (And.intro xaPos' ybNeg')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inr (And.intro xaPos' ybZero')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  =>
    nlinarith

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b := by
  match h with
  | Or.inl (And.intro h₁ h₂) => nlinarith
  | Or.inr (And.intro h₁ h₂) => nlinarith

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b := by
  match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
  | Or.inl xaNeg,           Or.inl ybNeg           =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inl (And.intro xaNeg' ybNeg')
  | Or.inl xaNeg,           Or.inr (Or.inl ybZero) =>
    have xaNeg' := le_of_lt xaNeg
    simp at xaNeg'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaNeg' ybZero')
  | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  =>
    nlinarith
  | Or.inr (Or.inl xaZero), Or.inl ybNeg           =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybNeg' := le_of_lt ybNeg
    simp at ybNeg'
    exact Or.inl (And.intro xaZero' ybNeg')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) =>
    have xaZero' := le_of_eq xaZero
    simp at xaZero'
    have ybZero' := le_of_eq ybZero
    simp at ybZero'
    exact Or.inl (And.intro xaZero' ybZero')
  | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  =>
    have xaZero' := ge_of_eq xaZero
    simp at xaZero'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inr (And.intro xaZero' ybPos')
  | Or.inr (Or.inr xaPos),  Or.inl ybNeg           =>
    nlinarith
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybZero' := ge_of_eq ybZero
    simp at ybZero'
    exact Or.inr (And.intro xaPos' ybZero')
  | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  =>
    have xaPos' := le_of_lt xaPos
    simp at xaPos'
    have ybPos' := le_of_lt ybPos
    simp at ybPos'
    exact Or.inr (And.intro xaPos' ybPos')

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b := by
  match h with
  | Or.inl (And.intro h₁ h₂) => nlinarith
  | Or.inr (And.intro h₁ h₂) => nlinarith

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Real
