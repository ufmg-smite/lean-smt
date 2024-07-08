/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Logic
import Batteries.Data.Rat

namespace Rat


section basics

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

protected theorem add_zero : ∀ a : Rat, a + 0 = a := by
  sorry

protected theorem add_assoc : ∀ a b c : Rat, a + b + c = a + (b + c) := by
  sorry

protected theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) := by
  sorry

@[simp]
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

end num_related



section le_lt_extra

variable {x y : Rat}

protected theorem le_refl : x ≤ x := by
  simp [Rat.le_iff_blt, Rat.blt]
  if h : x = 0 then
    simp [h]
    rw [← Rat.num_neg, Rat.zero_num]
    exact Int.lt_irrefl 0
  else
    simp [h]
    rw [← Rat.num_neg, ← Rat.num_pos]
    omega

protected theorem lt_irrefl : ¬ x < x := by
  simp [Rat.not_lt, Rat.le_refl]

protected theorem le_of_lt : x < y → x ≤ y := by
  intro h_lt
  apply Decidable.byContradiction
  intro h
  let _ := Rat.not_le.mp h
  let _ := Rat.lt_asymm h_lt
  contradiction

protected theorem ne_of_lt : x < y → x ≠ y := by
  intro h_lt h_eq
  exact Rat.lt_irrefl (h_eq ▸ h_lt)

end le_lt_extra



section nonneg

variable (x : Rat)

protected theorem nonneg_total : 0 ≤ x ∨ 0 ≤ -x := by
  rw [← num_nonneg (q := -x), ← num_nonneg (q := x)]
  rw [Rat.neg_num, Int.neg_nonneg]
  exact Int.le_total _ _

variable {x}

protected theorem nonneg_antisymm : 0 ≤ x → 0 ≤ -x → x = 0 := by
  rw [← Rat.num_eq_zero, ← Rat.num_nonneg, ← Rat.num_nonneg, Rat.num_neg_eq_neg_num]
  omega

end nonneg



section neg_sub

variable {x y : Rat}

protected theorem neg_sub : -(x - y) = y - x := by
  cases x with | mk' nx dx _ _ =>
  cases y with | mk' ny dy _ _ =>
  simp [Rat.sub_eq_add_neg, Neg.neg]
  simp [Rat.neg, Rat.divInt_ofNat, Rat.add_def, Rat.normalize_eq]
  rw [Nat.mul_comm dx dy]
  constructor
  · rw [← Int.neg_ediv_of_dvd]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.neg_sub]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]
    · conv => lhs ; arg 1 ; arg 2 ; rw [← Int.natAbs_ofNat (dy * dx)]
      exact Int.gcd_dvd_left
  · rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]

@[simp]
protected theorem sub_self : x - x = 0 :=
  numDenCasesOn' x fun nx dx h_dx => by
    rw [Rat.divInt_sub_divInt _ _ (Int.natCast_ne_zero.mpr h_dx) (Int.natCast_ne_zero.mpr h_dx)]
    simp

protected theorem add_neg_self : x + -x = 0 :=
  Rat.sub_eq_add_neg x x ▸ Rat.sub_self

protected theorem eq_neg_of_add_eq_zero_left : x + y = 0 → x = - y :=
  numDenCasesOn'' x fun nx dx h_dx h_dx_red =>
  numDenCasesOn'' y fun ny dy h_dy h_dy_red => by
    simp only [Rat.neg_divInt, Rat.add_def, Neg.neg]
    simp only [Rat.neg, normalize_eq_zero]
    simp only [eq_iff_mul_eq_mul, ← Int.neg_mul_eq_neg_mul]
    intro h
    apply Int.eq_neg_of_eq_neg
    exact Int.neg_eq_of_add_eq_zero h |>.symm

protected theorem le_iff_sub_nonneg (x y : Rat) : x ≤ y ↔ 0 ≤ y - x :=
  numDenCasesOn'' x fun nx dx h_dx _ =>
  numDenCasesOn'' y fun ny dy h_dy _ => by
    let dy_dx_nz : dy * dx ≠ 0 :=
      Nat.mul_ne_zero h_dy h_dx
    change Rat.blt _ _ = false ↔ _
    unfold Rat.blt
    simp only
      [ Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, Rat.not_lt, ite_eq_left_iff,
        not_and, Rat.not_le, ← Rat.num_nonneg ]
    if h : ny < 0 ∧ 0 ≤ nx then
      simp [h]
      simp only [Rat.sub_def, Rat.not_le, normalize_eq, Rat.neg]
      simp [← Rat.num_neg]
      apply Int.ediv_neg'
      · apply Int.sub_neg_of_lt
        apply Int.lt_of_lt_of_le (b := 0)
        · apply Int.mul_neg_of_neg_of_pos h.1
          apply Int.natCast_pos.mpr
          apply Nat.pos_of_ne_zero h_dx
        · apply Int.mul_nonneg h.2
          exact Int.zero_le_natCast
      · apply Int.natCast_pos.mpr
        apply Nat.pos_iff_ne_zero.mpr
        exact Nat.gcd_ne_zero_right dy_dx_nz
    else
      simp [h]
      split
      case isTrue nb_0 =>
        simp [nb_0, Rat.sub_eq_add_neg, Rat.zero_add, Rat.nonneg_sub_iff_nonpos, ← Rat.num_nonpos]
        exact Int.not_lt
      case isFalse nb_nz =>
        simp only [Rat.sub_def, normalize_eq, ← Rat.num_nonneg]
        if ny_pos : 0 < ny then
          simp [ny_pos]
          if h_na : 0 < nx then
            simp [Int.not_le.mpr h_na]
            rw [Int.not_lt]
            rw [← Int.sub_nonneg]
            apply Iff.symm
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz
          else
            let na_nonpos := Int.not_lt.mp h_na
            simp [na_nonpos]
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz |>.mpr
            · apply Int.sub_nonneg_of_le
              apply Int.le_trans (b := 0)
              apply Int.mul_nonpos_of_nonpos_of_nonneg
              · exact Int.not_lt.mp h_na
              · exact Int.natCast_nonneg
              · apply Int.mul_nonneg _ Int.natCast_nonneg
                exact Int.le_of_lt ny_pos
        else
          simp [ny_pos, Int.not_lt, ← Int.sub_nonneg]
          rw [Int.sub_zero]
          rw [Int.sub_zero]
          apply Iff.symm
          apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz

protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a := by
  rw [Rat.le_iff_sub_nonneg b a]

end neg_sub



section divInt

@[simp]
theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [
    ← Rat.num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd),
  ]

protected theorem divInt_le_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [Rat.sub_eq_add_neg, Rat.neg_divInt, Int.ne_of_gt b0, Int.ne_of_gt d0, Int.mul_pos d0 b0]
  rw [Rat.divInt_add_divInt]
  simp [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos d0 b0)]
  rw [← Int.sub_nonneg (a := c * b)]
  rw [Int.neg_mul, ← Int.sub_eq_add_neg]
  · apply Int.lt_iff_le_and_ne.mp d0 |>.2 |>.symm
  · apply Int.lt_iff_le_and_ne.mp b0 |>.2 |>.symm

end divInt

end Rat
