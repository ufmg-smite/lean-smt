/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Int.Core
import Smt.Reconstruct.Real.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Archimedean

namespace Smt.Reconstruct.Real.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t s x : Real}

theorem div_total_zero : x / 0 = 0 :=
  div_zero x

-- Eliminations

theorem elim_gt : (t > s) = ¬(s ≥ t) :=
  propext not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext not_le.symm
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext (Iff.symm antisymm_iff)

theorem eq_conflict {t : Int} {c : Real} (hcc : (↑⌊c⌋ = c) = False) : (t = c) = False := by
  simp only [eq_iff_iff, iff_false]
  intro htc
  have hcc : ⌊c⌋ < c := (le_iff_eq_or_lt.mp (Int.floor_le c)).resolve_left hcc.mp
  cases Int.lt_trichotomy t ⌊c⌋ <;> rename_i htcf
  · have hntc : ↑t ≠ c := (lt_iff_le_and_ne.mp (lt_trans (Int.cast_lt.mpr htcf) hcc)).right
    contradiction
  · cases htcf <;> rename_i htcf
    · simp_all
    · have h : c < t := by
        apply @lt_of_lt_of_le _ _ _
        · apply ((Int.floor_eq_iff (z := ⌊c⌋) (a := c)).mp rfl).right
        · rewrite [← Int.cast_one, ← Int.cast_add, Int.cast_le]
          exact htcf
      simp_all

theorem geq_tighten {t : Int} {c : Real} {cc : Int} (hc : (↑⌊c⌋ = c) = False) (hcc : cc = Int.addN [⌊c⌋, 1]) : (t ≥ c) = (t ≥ cc) := by
  simp only [hcc, Int.addN, ge_iff_le, eq_iff_iff, le_iff_eq_or_lt, ← Int.floor_lt]
  have h : ↑t ≠ c := by simpa [Eq.symm] using eq_conflict hc
  apply Iff.intro <;> intro hct
  · have h := hct.resolve_left h.symm
    omega
  · omega

-- Absolute value comparisons

theorem abs_eq : (|x| = |y|) = (x = y ∨ x = -y) := propext abs_eq_abs

theorem abs_gt : (|x| > |y|) = ite (x ≥ 0) (ite (y ≥ 0) (x > y) (x > -y)) (ite (y ≥ 0) (-x > y) (-x > -y)) := by
  split <;> rename_i hx <;> split <;> rename_i hy
  · rw [abs_eq_self.mpr hx, abs_eq_self.mpr hy]
  · rw [abs_eq_self.mpr hx, abs_eq_neg_self.mpr (le_of_not_ge hy)]
  · rw [abs_eq_neg_self.mpr (le_of_not_ge hx), abs_eq_self.mpr hy]
  · rw [abs_eq_neg_self.mpr (le_of_not_ge hx), abs_eq_neg_self.mpr (le_of_not_ge hy)]

-- ITE lifting

theorem geq_ite_lift [h : Decidable c] {t s r : Real} : (ite c t s ≥ r) = ite c (t ≥ r) (s ≥ r) := by
  cases h <;> simp_all

theorem leq_ite_lift [h : Decidable c] {t s r : Real} : (ite c t s ≤ r) = ite c (t ≤ r) (s ≤ r) := by
  cases h <;> simp_all

-- min/max rules

theorem min_lt1 : (ite (t < s) t s ≤ t) = True := by
  cases h : decide (t < s) <;>
  simp_all only [decide_eq_false_iff_not, ite_false, not_false_eq_true, not_lt.mp,
                 decide_eq_true_eq, ite_true, le_refl]

theorem min_lt2 : (ite (t < s) t s ≤ s) = True := by
  cases h : decide (t < s) <;>
  simp_all only [decide_eq_false_iff_not, ite_false, le_refl,
                 decide_eq_true_eq, ite_true, le_of_lt]

theorem max_geq1 : (ite (t ≥ s) t s ≥ t) = True := by
  cases h : decide (t ≥ s) <;>
  simp_all only [ge_iff_le, decide_eq_false_iff_not, ite_false, not_false_eq_true, le_of_not_ge,
                 decide_eq_true_eq, ite_true, le_refl]

theorem max_geq2 : (ite (t ≥ s) t s ≥ s) = True := by
  cases h : decide (t ≥ s) <;>
  simp_all only [ge_iff_le, decide_eq_false_iff_not, ite_false, le_refl,
                 decide_eq_true_eq, ite_true]

theorem arith_sine_zero : Real.sin 0 = 0 := Real.sin_zero
theorem arith_sine_pi2 : Real.sin ((1/2) * Real.pi) = 1 := by
  have : 1 / 2 * Real.pi = Real.pi / 2 := one_div_mul_eq_div 2 Real.pi
  rw [this]
  exact Real.sin_pi_div_two

theorem arith_cosine_elim (x : Real) : Real.cos x = Real.sin ((1/2) * Real.pi - x) := by
  have : 1 / 2 * Real.pi = Real.pi / 2 := one_div_mul_eq_div 2 Real.pi
  rw [this]
  exact Eq.symm (Real.sin_pi_div_two_sub x)

theorem arith_tangent_elim (x : Real) : Real.tan x = Real.sin x / Real.cos x := Real.tan_eq_sin_div_cos x
theorem arith_cotangent_elim (x : Real) : Real.cot x = Real.cos x / Real.sin x := Real.cot_eq_cos_div_sin x

-- TODO: Secant and cosecant. There is no definition for those in mathlib. Should we define our own?

end Smt.Reconstruct.Real.Rewrite
