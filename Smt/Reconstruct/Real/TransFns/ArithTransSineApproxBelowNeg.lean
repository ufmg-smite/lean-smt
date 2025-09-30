/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_BELOW_NEGE
-/

import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowPos

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineApproxBelowNeg_self (d k : Nat) (x : ℝ) (hd : d = 2*k + 1) (hx : x ≤ 0) :
  taylorWithinEval Real.sin d Set.univ 0 x - x ^ (d + 1) / (d + 1).factorial ≤ sin x := by
  cases' lt_or_eq_of_le hx with hx hx
  · have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
    rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
    rw [←sub_nonneg, ←sub_add, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
    rw [sub_zero, mul_div_assoc, ← add_one_mul]
    apply mul_nonneg _ _
    · rw [←neg_le_iff_add_nonneg', neg_le]; apply neg_one_le_iteratedDeriv_sin
    · apply mul_nonneg (le_of_lt (Even.pow_pos (by rw [hd]; norm_num) (by linarith))) (by simp)
  · simp [hx]

theorem arithTransSineApproxBelowNeg (d k : ℕ) (lb ub x c : ℝ) (hd : d = 2*k + 1)
                                     (hl : -π ≤ lb) (hu : ub ≤ 0)
                                     (hx1 : lb ≤ x) (hx2 : x ≤ ub)
                                     (hc : c = if -π/2 < lb then lb else if - π/2 < ub then - π/2 else ub) :
  taylorWithinEval Real.sin d Set.univ 0 c - c ^ (d + 1) / (d + 1).factorial ≤ sin x := by
  have : c ≤ 0 := by split_ifs at hc <;> linarith
  apply le_trans (arithTransSineApproxBelowNeg_self d k c hd this)
  split_ifs at hc with h1 h2
  · apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith
  · rw [hc, neg_div, sin_neg, sin_pi_div_two]; apply neg_one_le_sin
  · rw [←neg_le_neg_iff, ←sin_neg c, ←sin_neg, ←sin_pi_sub, ←sin_pi_sub (-c)]
    apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith

theorem arithTransSineApproxBelowNegComp (d k : ℕ) (lb ub x c evalC : ℝ) (hd : d = 2*k + 1)
    (hc' : evalC = sinTaylor d c - c ^ (d + 1) / (d + 1).factorial)
    (hl : -π ≤ lb) (hu : ub ≤ 0)
    (hc : c = if -π/2 < lb then lb else if - π/2 < ub then - π/2 else ub) :
    (x ≥ lb ∧ x ≤ ub) → evalC ≤ sin x := by
  rintro ⟨hx1, hx2⟩
  rw [hc', <- sinEmbedding]
  exact arithTransSineApproxBelowNeg d k lb ub x c hd hl hu hx1 hx2 hc

end Smt.Reconstruct.Real.TransFns
