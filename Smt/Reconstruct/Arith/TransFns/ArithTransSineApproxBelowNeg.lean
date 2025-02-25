/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/


import Smt.Reconstruct.Arith.TransFns.ArithTransSineApproxBelowPos

open Set Real

namespace Smt.Reconstruct.Arith

theorem arithTransSineApproxBelowNeg (d k : Nat) (hd : d = 4*k + 1) (hx : x < 0) (hx2 : -π ≤ x):
  let p : ℕ → ℝ → ℝ := fun d => taylorWithinEval Real.sin d Set.univ 0
  p d x ≤ sin x := by
  intro p
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
  rw [←sub_nonneg, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  have : (d+1)%4 = 2 := by simp [hd, Nat.add_mod]
  simp only [this, iteratedDeriv_sin_cos, reduceIte, one_ne_zero, sub_zero, show 1 ≠ 3 by decide, show 1 ≠ 2 by decide, two_ne_zero, show 2 ≠ 1 by decide]
  apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
  simp only [Pi.neg_apply, neg_mul, Left.nonneg_neg_iff]
  apply mul_nonpos_of_nonpos_of_nonneg (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (le_of_lt (mem_Ioo.mp hx').2) (le_trans hx2 (le_of_lt (mem_Ioo.mp hx').1)))
  apply Even.pow_nonneg (by rw [even_iff_two_dvd]; omega)
