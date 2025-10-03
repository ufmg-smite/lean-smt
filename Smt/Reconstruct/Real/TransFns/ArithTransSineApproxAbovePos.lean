/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_ABOVE_POSE
-/

import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowNeg
import Mathlib.Analysis.Real.Pi.Bounds

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineApproxAbovePos' (d k : ℕ) (x : ℝ) (hd : d = 2*k + 1)
                                     (hx1 : 0 ≤ x) :
    Real.sin x ≤ taylorWithinEval Real.sin d Set.univ 0 x + x ^ (d + 1) / (d + 1).factorial := by
  rw [← neg_neg x, sin_neg, taylorSin_neg, neg_add_eq_sub, ←neg_sub, neg_le_neg_iff, Even.neg_pow (by rw [hd]; norm_num)]
  apply arithTransSineApproxBelowNeg_self d k (-x) hd (by linarith)

theorem arithTransSineApproxAbovePos (d k : ℕ) (lb ub x c : ℝ) (hd : d = 2*k + 1)
                                     (hl : 0 ≤ lb) (hu : ub ≤ π)
                                     (hx1 : lb ≤ x) (hx2 : x ≤ ub)
                                     (hc : c = if ub < π/2 then ub else if lb < π/2 then π/2 else lb) :
    Real.sin x ≤ taylorWithinEval Real.sin d Set.univ 0 c + c ^ (d + 1) / (d + 1).factorial := by
  have : 0 ≤ c := by split_ifs at hc <;> linarith
  apply le_trans _ (arithTransSineApproxAbovePos' d k c hd this)
  split_ifs at hc with h1 h2
  · apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith
  · rw [hc, sin_pi_div_two]; apply sin_le_one
  · rw [← sin_pi_sub, ← sin_pi_sub c]
    apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith

theorem arithTransSineApproxAbovePosComp (d k : ℕ) (lb ub x c evalC : ℝ) (hd : d = 2*k + 1)
    (hl : 0 ≤ lb) (hu : ub ≤ π)
    (hc' : evalC = sinTaylor d c + c ^ (d + 1) / (d + 1).factorial)
    (hc : c = if ub < π/2 then ub else if lb < π/2 then π/2 else lb) :
    (x ≥ lb ∧ x ≤ ub) → Real.sin x ≤ evalC := by
  rintro ⟨hx1, hx2⟩
  rw [hc', <- sinEmbedding]
  exact arithTransSineApproxAbovePos d k lb ub x c hd hl hu hx1 hx2 hc

end Smt.Reconstruct.Real.TransFns
