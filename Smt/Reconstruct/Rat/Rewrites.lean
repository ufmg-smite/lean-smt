/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Batteries.Data.Rat
import Smt.Reconstruct.Rat.Lemmas

namespace Smt.Reconstruct.Rat.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t s x : Rat}

theorem div_total_zero : t / 0 = 0 :=
  Rat.div_def t 0 ▸ Rat.inv_zero.symm ▸ Rat.mul_zero t

-- Eliminations

theorem elim_gt : (t > s) = ¬(s ≥ t) :=
  propext Rat.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Rat.not_le.symm
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) := by
  rw [←elim_leq, ←elim_leq, Rat.le_iff_sub_nonneg _ _]

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) := by
  apply propext
  rw [←elim_leq, And.comm]
  exact Rat.le_antisymm_iff _ _

theorem eq_conflict {t : Int} {c : Rat} (hcc : (↑c.floor = c) = False) : (t = c) = False := by
  simp only [eq_iff_iff, iff_false]
  intro htc
  have hcc : c.floor < c := ((Rat.le_iff_eq_or_lt c.floor c).mp (Rat.floor_le_self c)).resolve_left hcc.mp
  cases Int.lt_trichotomy t c.floor <;> rename_i htcf
  · have hntc : ↑t ≠ c := (Rat.lt_iff_le_and_ne.mp (Rat.lt_trans (Rat.cast_lt2 htcf) hcc)).right
    contradiction
  · cases htcf <;> rename_i htcf
    · simp_all
    · have h : c < t := by
        apply @Rat.lt_of_lt_of_le _ _ _
        · exact Rat.self_le_floor_add_one c
        · exact Rat.cast_le2 htcf
      simp_all [Rat.lt_irrefl]

theorem geq_tighten {t : Int} {c : Rat} {cc : Int} (hc : (↑c.floor = c) = False) (hcc : cc = Int.addN [c.floor, 1]) : (t ≥ c) = (t ≥ cc) := by
  have Int.floor_lt {z : Int} {a : Rat} : a.floor < z ↔ a < ↑z := sorry
  simp only [hcc, Int.addN, ge_iff_le, eq_iff_iff, Rat.le_iff_eq_or_lt, ← Int.floor_lt]
  have h : ↑t ≠ c := by simpa [Eq.symm] using eq_conflict hc
  apply Iff.intro <;> intro hct
  · have h := hct.resolve_left h.symm
    omega
  · omega

-- Absolute value comparisons

theorem abs_eq : (x.abs = y.abs) = (x = y ∨ x = -y) := by
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Rat.abs] <;> sorry

theorem abs_gt : (x.abs > y.abs) = ite (x ≥ 0) (ite (y ≥ 0) (x > y) (x > -y)) (ite (y ≥ 0) (-x > y) (-x > -y)) := by
  simp only [Rat.abs, gt_iff_lt, ge_iff_le, eq_iff_iff] <;> split <;> split <;> split <;> split <;> sorry

-- ITE lifting

theorem geq_ite_lift [h : Decidable c] {t s r : Rat} : (ite c t s ≥ r) = ite c (t ≥ r) (s ≥ r) := by
  cases h <;> simp_all

theorem leq_ite_lift [h : Decidable c] {t s r : Rat} : (ite c t s ≤ r) = ite c (t ≤ r) (s ≤ r) := by
  cases h <;> simp_all

-- min/max rules

theorem min_lt1 : (ite (t < s) t s ≤ t) = True := by
  cases h : decide (t < s) <;> simp_all [Rat.not_lt.mp]

theorem min_lt2 : (ite (t < s) t s ≤ s) = True := by
  cases h : decide (t < s) <;> simp_all [Rat.le_of_lt]

theorem max_geq1 : (ite (t ≥ s) t s ≥ t) = True := by
  cases h : decide (t ≥ s) <;> simp_all [Rat.le_of_not_le]

theorem max_geq2 : (ite (t ≥ s) t s ≥ s) = True := by
  cases h : decide (t ≥ s) <;> simp_all

end Smt.Reconstruct.Rat.Rewrite
