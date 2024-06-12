/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

private theorem Nat.mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases Nat.mod_two_eq_zero_or_one n <;> rename_i h <;> simp [h]

private theorem Nat.even_add : (m + n) % 2 = 0 ↔ (m % 2 = 0 ↔ n % 2 = 0) := by
  cases Nat.mod_two_eq_zero_or_one m <;> rename_i h₁ <;> cases Nat.mod_two_eq_zero_or_one n <;> rename_i h₂ <;>
    simp [h₁, h₂, Nat.add_mod]

private theorem Nat.even_add_one : (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 := by
  simp [Nat.even_add]

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
  have ⟨ ht₁, ht₂ ⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Int

variable {a b c d : Int}

private theorem or_implies_left (hpq : p ∨ q) (hnq : ¬q) : p := by
  cases hpq with
  | inl hp => exact hp
  | inr hq => exact False.elim (hnq hq)

private theorem or_implies_right (hpq : p ∨ q) (hnp : ¬p) : q := by
  cases hpq with
  | inl hp => exact False.elim (hnp hp)
  | inr hq => exact hq

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have r₁: a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂: a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_trans r₁ r₂

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have r₁: a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂: a + d < b + d := Int.add_lt_add_right h₁ d
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

theorem trichotomy₁ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_right (or_implies_right tr (Int.not_lt.mpr h₁)) h₂

theorem trichotomy₂ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_right (or_implies_right tr (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₃ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_left (or_implies_right tr (Int.not_lt.mpr h₁)) (Int.not_lt.mpr h₂)

theorem trichotomy₄ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_left (or_implies_right tr (Int.not_lt.mpr h₂)) (Int.not_lt.mpr h₁)

theorem trichotomy₅ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_left (or_implies_left (or_assoc.mpr tr) (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₆ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact or_implies_left (or_implies_left (or_assoc.mpr tr) (Int.not_lt.mpr h₁)) h₂

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

mutual

theorem pow_neg_even {k : Nat} {z : Int} (h₁ : z < 0) (h₂ : k % 2 = 0) : z ^ k > 0 := by
  cases k with
  | zero    => simp [Int.pow_zero]
  | succ k =>
    have hodd := Nat.even_add_one.mp h₂
    have mulZ : z * z ^ k > z * 0 := Int.mul_lt_mul_of_neg_left (pow_neg_odd h₁ (Nat.mod_two_ne_zero.mp hodd)) h₁
    simp at mulZ
    rw [Int.pow_succ, Int.mul_comm]
    exact mulZ

theorem pow_neg_odd {k : Nat} {z : Int} (h₁ : z < 0) (h₂ : k % 2 = 1) : z ^ k < 0 := by
  cases k with
  | zero    => simp at h₂
  | succ k =>
    have heven : k % 2 = 0 := Classical.not_not.mp (mt Nat.even_add_one.mpr (Eq.symm h₂ ▸ nofun))
    have mulZ : z * 0 > z * z ^ k := Int.mul_lt_mul_of_neg_left (pow_neg_even h₁ heven) h₁
    simp at mulZ
    rw [Int.pow_succ, Int.mul_comm]
    exact mulZ

end

theorem pow_pos {k : Nat} {z : Int} (h : z > 0) : z ^ k > 0 := by
  induction k with
  | zero    => simp [Int.pow_zero]
  | succ k ih =>
    rw [Int.pow_succ]
    have h₂ := Int.mul_lt_mul_of_pos_left h ih
    simp at h₂
    exact h₂

theorem non_zero_even_pow {k : Nat} {z : Int} (h₁ : z ≠ 0) (h₂ : k % 2 = 0) : z ^ k > 0 := by
  match Int.lt_trichotomy z 0 with
  | Or.inl hneg => exact pow_neg_even hneg h₂
  | Or.inr (Or.inl hzero) => rw [hzero] at h₁; simp at h₁
  | Or.inr (Or.inr hpos)  => exact pow_pos hpos

theorem combine_signs₁ : a > 0 → b > 0 → b * a > 0 := by
  intros h₁ h₂
  have h := Int.mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combine_signs₂ : a > 0 → b < 0 → b * a < 0 := by
  intros h₁ h₂
  have h := Int.mul_lt_mul_of_pos_right h₂ h₁
  simp at h
  exact h

theorem combine_signs₃ : a < 0 → b > 0 → b * a < 0 := by
  intros h₁ h₂
  have h := Int.mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combine_signs₄ : a < 0 → b < 0 → b * a > 0 := by
  intros h₁ h₂
  have h := Int.mul_lt_mul_of_neg_left h₁ h₂
  simp at h
  exact h

theorem arith_mul_pos_lt : c > 0 ∧ a < b → c * a < c * b :=
  uncurry (flip Int.mul_lt_mul_of_pos_left)

theorem arith_mul_pos_le : c > 0 ∧ a ≤ b → c * a ≤ c * b := λ h =>
  Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem arith_mul_pos_gt : c > 0 ∧ a > b → c * a > c * b := arith_mul_pos_lt

theorem arith_mul_pos_ge : c > 0 ∧ a ≥ b → c * a ≥ c * b := arith_mul_pos_le

theorem arith_mul_pos_eq : c > 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

theorem arith_mul_neg_lt : c < 0 ∧ a < b → c * a > c * b :=
  uncurry (flip Int.mul_lt_mul_of_neg_left)

theorem arith_mul_neg_le : c < 0 ∧ a ≤ b → c * a ≥ c * b := λ h =>
  Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem arith_mul_neg_gt : c < 0 ∧ a > b → c * a < c * b := arith_mul_neg_lt

theorem arith_mul_neg_ge : c < 0 ∧ a ≥ b → c * a ≤ c * b := arith_mul_neg_le

theorem arith_mul_neg_eq : c < 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

end Smt.Reconstruct.Int
