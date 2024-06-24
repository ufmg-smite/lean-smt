/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

private theorem Int.mul_lt_mul_left {c x y : Int} (hc : c > 0) : (c * x < c * y) = (x < y) := by
  apply propext
  constructor
  · apply Int.lt_of_mul_lt_mul_left (h := Int.le_of_lt hc)
  · apply Int.mul_lt_mul_of_pos_left (h₂ := hc)

private theorem Int.mul_le_mul_left {c x y : Int} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  apply propext
  constructor
  · apply le_of_mul_le_mul_left (h := hc)
  · apply Int.mul_le_mul_of_nonneg_left (h₂ := Int.le_of_lt hc)

private theorem Int.mul_eq_zero_left {x y : Int} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  rewrite [Int.mul_eq_zero] at hxy
  exact hxy.resolve_left hx

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Int

variable {a b c d : Int}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_trans r₁ r₂

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_of_le_of_lt r₁ r₂

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  exact Int.add_lt_add_right h₁ d

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.lt_of_lt_of_le r₁ r₂

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.le_trans r₁ r₂

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂]
  exact Int.add_le_add_right h₁ d

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁]
  exact Int.add_lt_add_left h₂ b

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact Int.add_le_add_left h₂ b

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₁, h₂]
  exact Int.le_refl (b + d)

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c - 1 :=
  Int.le_sub_one_of_lt h

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c + 1 :=
  h

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₁)) h₂

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₂)) (Int.not_lt.mpr h₁)

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₁)) (Int.not_lt.mpr h₂)

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₁)) h₂

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply Int.sub_neg_of_lt
  · apply Int.lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact Int.sub_nonpos_of_le
  · exact Int.le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [Int.sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact Int.sub_nonneg_of_le
  · exact Int.le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact Int.sub_pos_of_lt
  · exact Int.lt_of_sub_pos

theorem lt_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem eq_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) = 0) = (x - y = 0) := by
    apply propext; constructor
    · apply Int.mul_eq_zero_left (Int.ne_of_gt hc)
    · intro hxy; rw [hxy, Int.mul_zero]
  rw [@eq_eq_sub_eq_zero a₁, @eq_eq_sub_eq_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, ge_iff_le, Int.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, gt_iff_lt, Int.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_neg_right ha hb
  simp at h
  exact h

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_right ha hb
  simp at h
  exact h

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  match Int.lt_trichotomy a 0 with
  | .inl hn         => mul_sign₁ hn hn
  | .inr (.inl hz)  => absurd hz ha
  | .inr (.inr hp)  => mul_sign₆ hp hp

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₄ (mul_sign₁ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₃ (mul_sign₃ ha hp) hp

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₁ (mul_sign₄ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₆ (mul_sign₆ ha hp) hp

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  Int.mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  Int.mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

end Smt.Reconstruct.Int
