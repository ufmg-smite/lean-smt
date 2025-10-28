/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_NEGE
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.Exponential

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxBelow
import Smt.Reconstruct.Real.TransFns.TaylorComp

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem le_of_ConvexOn {s : Set ℝ} {x z t : ℝ} (f : ℝ → ℝ) (hf : ConvexOn Real s f) (hx : x ∈ s) (hz : z ∈ s)
                        (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxz : x ≤ z):
  f (t*x + (1-t)*z) ≤ t*(f x) + (1-t)*(f z) := by
  cases' eq_or_lt_of_le hxz with hxz hxz
  · rw [hxz]; ring_nf; simp
  · cases' eq_or_lt_of_le' ht0 with ht0 ht0
    · simp [ht0]
    · cases' eq_or_lt_of_le' ht1 with ht1 ht1
      · simp [← ht1]
      · have := ConvexOn.secant_mono_aux2 hf hx hz
                (Eq.trans_lt
                  (by ring)
                  ((add_lt_add_iff_left _).mpr ((mul_lt_mul_iff_right₀ (by linarith)).mpr hxz))) (show t*x + (1-t)*z < z by
                    apply Eq.trans_gt
                          (by ring)
                          ((add_lt_add_iff_right _).mpr ((mul_lt_mul_iff_right₀ (by linarith)).mpr hxz)))
        rw [show t*x + (1-t)*z -x = (1-t)*(z-x) by linarith, div_mul_eq_div_div] at this
        rw [div_le_div_iff_of_pos_right (by linarith), div_le_iff₀ (by linarith)] at this
        linarith

theorem le_secant {l t u : ℝ} (p : ℝ → ℝ) (ht : l ≤ t ∧ t ≤ u) :
  let C := (t-l)/(u-l)
  ((p l - p u) / (l - u)) * (t - l) + p l = C * p u + (1 - C) * p l ∧ 0 ≤ C ∧ C ≤ 1 := by
  intro C
  have hc : C = (t-l)/(u-l) := rfl
  rw [← neg_div_neg_eq, neg_sub, neg_sub, mul_comm_div]
  constructor
  rw [sub_mul, sub_add_eq_add_sub, ← mul_one (p l), mul_assoc, add_sub_assoc, ←mul_sub (p l)]
  rw [one_mul, mul_one, mul_comm C, mul_comm (1-C)]
  rw [hc]
  simp only [true_and, div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr (le_trans ht.1 ht.2))]
  apply div_le_one_of_le₀ (by linarith) (by linarith)

-- write a theorem here where if f ≤ p then f t ≤ secant...
theorem le_convex_of_le {s : Set ℝ} {l u t : ℝ} {f p : ℝ → ℝ} (ht : l ≤ t ∧ t ≤ u) (hl : f l ≤ p l) (hu : f u ≤ p u) (hf : ConvexOn Real s f) (hl1 : l ∈ s) (hu1 : u ∈ s) :
  f t ≤ ((p l - p u) / (l - u)) * (t - l) + p l:= by
  have ⟨hp1, hC1, hC2⟩ := le_secant p ht
  rw [hp1]
  set C := (t-l)/(u-l)
  cases' (lt_or_eq_of_le (le_trans ht.1 ht.2)) with hlu hlu
  · have H3 := le_of_ConvexOn f hf hl1 hu1 (show 0 ≤ 1 - C by linarith) (by linarith) (le_of_lt hlu)
    have htt : (1-C) * l + (1-(1-C)) * u = t := by
      simp only [sub_sub_cancel, C]
      field_simp [show u -l ≠ 0 by linarith]
      linarith
    rw [htt, sub_sub_self, add_comm] at H3
    apply le_trans H3
    apply add_le_add (mul_le_mul_of_nonneg_left hu hC1) (mul_le_mul_of_nonneg_left hl (by linarith))
  · simp [hlu, (show t = u by linarith)]
    linarith

theorem arithTransExpApproxAboveNeg (d k : Nat) (hd : d = 2*k) (l u t : ℝ) (ht : l ≤ t ∧ t ≤ u) (hu : u < 0):
  let p: ℝ → ℝ := taylorWithinEval Real.exp d Set.univ 0
  Real.exp t ≤ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.exp d Set.univ 0 x := fun _ => rfl
  apply le_convex_of_le ht
        (by rw [hp]; exact expApproxAbove d k hd (lt_of_le_of_lt (le_trans ht.1 ht.2) hu))
        (by rw [hp]; exact expApproxAbove d k hd hu)
        convexOn_exp (Set.mem_univ _) (Set.mem_univ _)

theorem arithTransExpApproxAboveNeg' (d k : Nat) (l u t : ℝ) (evalL evalU : ℝ) (hl : taylorWithinEval Real.exp d Set.univ 0 l = evalL) (hu : taylorWithinEval Real.exp d Set.univ 0 u = evalU) (hd : d = 2 * k) (hu' : u < 0):
  t ≥ l ∧ t ≤ u → Real.exp t ≤ evalL + ((evalL - evalU) / (l - u)) * (t - l) := by
  intro ht
  rw [add_comm, <- hl, <- hu]
  exact arithTransExpApproxAboveNeg d k hd l u t ht hu'

theorem arithTransExpApproxAboveNegComp (d k : Nat) (l u t : ℝ) (evalL evalU : ℝ) (hl : expTaylor d l = evalL) (hu : expTaylor d u = evalU) (hd : d = 2 * k) (hu' : u < 0):
    t ≥ l ∧ t ≤ u → Real.exp t ≤ evalL + ((evalL - evalU) / (l - u)) * (t - l) := by
  rw [<- expEmbedding] at hl
  rw [<- expEmbedding] at hu
  exact fun a => arithTransExpApproxAboveNeg' d k l u t evalL evalU hl hu hd hu' a

end Smt.Reconstruct.Real.TransFns
