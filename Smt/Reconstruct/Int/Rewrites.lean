/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Int.Core

namespace Smt.Reconstruct.Int.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t s x : Int}

theorem div_total : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem div_total_one : t / 1 = t :=
  Int.ediv_one t
theorem div_total_zero : t / 0 = 0 :=
  Int.ediv_zero t

theorem div_total_neg : t / s = -(t / -s) :=
  Int.ediv_neg t s ▸ Int.neg_neg _ ▸ rfl

theorem mod_total : s ≠ 0 → t % s = t % s :=
  const _ rfl
theorem mod_total_one : t % 1 = 0 :=
  Int.emod_one t
theorem mod_total_zero : t % 0 = t :=
  Int.emod_zero t

theorem mod_total_neg : t % s = t % -s :=
  Int.emod_neg t s ▸ rfl

-- Eliminations

theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  propext Int.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Int.not_le.symm
theorem elim_gt_add_one : (t > s) = (t ≥ s + 1) :=
  propext Int.lt_iff_add_one_le
theorem elim_lt_add_one : (t < s) = (s ≥ t + 1) :=
  propext Int.lt_iff_add_one_le
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem leq_norm : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨fun hts => Int.not_le.mpr (Int.add_le_add_right hts _),
           Int.not_lt.mp⟩

theorem geq_tighten : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨Int.sub_nonneg_of_le, Int.le_of_sub_nonneg⟩

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext ⟨Int.neg_le_neg, Int.le_of_neg_le_neg⟩

theorem refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_lt : (t < t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩
theorem refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_gt : (t > t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext ⟨(· ▸ And.intro (Int.le_refl t) (Int.le_refl t)), fun ⟨hst, hts⟩ => Int.le_antisymm hts hst⟩

theorem plus_flatten : Int.addN (xs ++ ([Int.addN (w :: ys)] ++ zs)) = Int.addN (xs ++ (w :: ys ++ zs)) := by
  simp only [Int.addN_append]
  rfl

theorem mult_flatten : Int.mulN (xs ++ ([Int.mulN (w :: ys)] ++ zs)) = Int.mulN (xs ++ (w :: ys ++ zs)) := by
  simp only [Int.mulN_append]
  rfl

theorem abs_elim : x.abs = if x < 0 then -x else x :=
  rfl

theorem mod_over_mod : c ≠ 0 → Int.addN (ts ++ ([r % c] ++ ss)) % c = Int.addN (ts ++ ([r] ++ ss)) % c := by
  simp only [Int.addN, Int.addN_append, Int.emod_add_cancel_left, Int.emod_add_cancel_right, Int.emod_emod, implies_true]

theorem divisible_elim {n t : Int} (_ : n ≠ 0) : (n ∣ t) = (t % n = 0) :=
  propext Int.dvd_iff_emod_eq_zero

-- Absolute value comparisons

theorem abs_eq : (x.abs = y.abs) = (x = y ∨ x = -y) := by
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Int.abs] <;> omega

theorem abs_gt : (x.abs > y.abs) = ite (x ≥ 0) (ite (y ≥ 0) (x > y) (x > -y)) (ite (y ≥ 0) (-x > y) (-x > -y)) := by
  simp only [Int.abs, gt_iff_lt, ge_iff_le, eq_iff_iff] <;> split <;> split <;> split <;> split <;> omega

-- ITE lifting

theorem geq_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s ≥ r) = ite c (t ≥ r) (s ≥ r) := by
  cases h <;> simp_all

theorem gt_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s > r) = ite c (t > r) (s > r) := by
  cases h <;> simp_all

theorem leq_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s ≤ r) = ite c (t ≤ r) (s ≤ r) := by
  cases h <;> simp_all

theorem lt_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s < r) = ite c (t < r) (s < r) := by
  cases h <;> simp_all

-- min/max rules

theorem min_lt1 : (ite (t < s) t s ≤ t) = True := by
  cases h : decide (t < s) <;> simp_all [Int.not_lt.mp]

theorem min_lt2 : (ite (t < s) t s ≤ s) = True := by
  cases h : decide (t < s) <;> simp_all [Int.le_of_lt]

theorem max_geq1 : (ite (t ≥ s) t s ≥ t) = True := by
  cases h : decide (t ≥ s) <;> simp_all [Int.le_of_not_le]

theorem max_geq2 : (ite (t ≥ s) t s ≥ s) = True := by
  cases h : decide (t ≥ s) <;> simp_all

end Smt.Reconstruct.Int.Rewrite
