/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_ABOVE_NEGE
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAbovePos
import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAboveNeg
import Smt.Reconstruct.Arith.TransFns.Utils

open Set Real

namespace Smt.Reconstruct.Arith

theorem sineApproxAboveNeg (d k : Nat) (hd : d = 4*k + 3) (hx : x < 0) (hx2 : -π ≤ x):
  let p : ℕ → ℝ → ℝ := fun d => taylorWithinEval Real.sin d Set.univ 0
  sin x ≤ p d x := by
  intro p
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H

  rw [←sub_nonpos, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  have : (d+1)%4 = 0 := by simp [hd, Nat.add_mod]
  simp only [this, iteratedDeriv_sin_cos, reduceIte, three_ne_zero, sub_zero, show 3 ≠ 1 by decide, show 3 ≠ 0 by decide, show 3 ≠ 2 by decide]
  apply mul_nonpos_of_nonpos_of_nonneg _ (by apply inv_nonneg.mpr; simp)
  apply mul_nonpos_of_nonpos_of_nonneg (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (le_of_lt (mem_Ioo.mp hx').2) (le_trans hx2 (le_of_lt (mem_Ioo.mp hx').1)))
  apply Even.pow_nonneg (by rw [even_iff_two_dvd]; omega)

theorem arithTransSineApproxAboveNeg (d k : Nat) (hd : d = 4*k + 3) (l u t : ℝ)
                                     (ht : l ≤ t ∧ t ≤ u) (hu : u < 0) (hl : -π ≤ l) :
  let p: ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
  Real.sin t ≤ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.sin d Set.univ 0 x := by simp
  apply le_convex_of_le ht
        (by rw [hp]; exact sineApproxAboveNeg d k hd (by linarith) hl)
        (by rw [hp]; exact sineApproxAboveNeg d k hd hu (by linarith))
        convexOn_sin_Icc (mem_Icc.mpr ⟨hl, by linarith⟩)
                         (mem_Icc.mpr ⟨by linarith, le_of_lt hu⟩)
