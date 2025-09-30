/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_BELOW_POSE
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAboveNeg

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem concaveIccSubset {f : ℝ → ℝ} {l1 r1 l2 r2 : ℝ} : ConcaveOn ℝ (Icc l2 r2) f → Icc l1 r1 ⊆ Icc l2 r2 → ConcaveOn ℝ (Icc l1 r1) f := by
  intros h1 h2
  exact ConcaveOn.subset h1 h2 (convex_Icc l1 r1)

theorem sineApproxBelowPos {x : ℝ} (d : Nat) (hx : 0 ≤ x):
  let p : ℕ → ℝ → ℝ := fun d x => taylorWithinEval Real.sin d Set.univ 0 x - (x ^ (d + 1) / (d + 1).factorial)
  p d x ≤ sin x := by
  intro p; simp only [tsub_le_iff_right, p]
  cases' lt_or_eq_of_le hx with hx hx
  · have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange (n := d) hx (ContDiff.contDiffOn contDiff_sin) (DifferentiableOn_iteratedDerivWithin contDiff_sin hx)
    have : taylorWithinEval sin d (Icc 0 x) 0 = taylorWithinEval sin d Set.univ 0 := by
      apply taylorWithinEval_eq
      · simp; exact le_of_lt hx
      · exact uniqueDiffOn_Icc hx
      · exact contDiff_sin
    rw [this] at H
    rw [←sub_nonpos]
    apply neg_le_neg_iff.mp
    rw [neg_sub, add_sub_right_comm, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
    rw [neg_zero, sub_zero, mul_div_assoc, ← add_one_mul]
    apply mul_nonneg _ _
    · rw [←neg_le_iff_add_nonneg', neg_le]; apply neg_one_le_iteratedDeriv_sin
    · apply mul_nonneg (le_of_lt (pow_pos hx (d + 1))) (by simp)
  · simp [<- hx]

theorem ge_of_ConcaveOn {x z t : Real} {s : Set Real} (f : ℝ → ℝ) (hf : ConcaveOn Real s f) (hx : x ∈ s) (hz : z ∈ s)
                        (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxz : x ≤ z):
    f (t*x + (1-t)*z) ≥ t*(f x) + (1-t)*(f z) := by
  have : ConvexOn Real s (-f) := neg_convexOn_iff.mpr hf
  have := le_of_ConvexOn (-f) this hx hz ht0 ht1 hxz
  simp_all
  linarith

theorem ge_concave_of_ge {s : Set Real} {l u t : ℝ} {f p : ℝ → ℝ} (ht : l ≤ t ∧ t ≤ u) (hl : p l ≤ f l) (hu : p u ≤ f u) (hf : ConcaveOn Real s f) (hl1 : l ∈ s) (hu1 : u ∈ s) :
    f t ≥ ((p l - p u) / (l - u)) * (t - l) + p l:= by
  have ⟨hp1, hC1, hC2⟩ := le_secant p ht
  rw [hp1]
  set C := (t-l)/(u-l)
  cases' (lt_or_eq_of_le (le_trans ht.1 ht.2)) with hlu hlu
  · have H3 := ge_of_ConcaveOn f hf hl1 hu1 (show 0 ≤ 1 - C by linarith) (by linarith) (le_of_lt hlu)
    have htt : (1-C) * l + (1-(1-C)) * u = t := by
      simp only [sub_sub_cancel, C]
      field_simp [show u -l ≠ 0 by linarith]
      linarith
    rw [htt, sub_sub_self, add_comm] at H3
    apply ge_trans H3
    apply add_le_add (mul_le_mul_of_nonneg_left hu hC1) (mul_le_mul_of_nonneg_left hl (by linarith))
  · simp [hlu, (show t = u by linarith)]
    linarith

theorem arithTransSineApproxBelowPos (d : ℕ) (t l u : ℝ) (ht : l ≤ t ∧ t ≤ u)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi) :
    let p : ℝ → ℝ := fun x => taylorWithinEval Real.sin d Set.univ 0 x - (x ^ (d + 1) / (d + 1).factorial)
    sin t ≥ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p; simp only [p]
  exact ge_concave_of_ge (l := l) (u := u) (t := t) (p := p) (f := sin) (s := Icc l u) ht
        (sineApproxBelowPos d hl)
        (sineApproxBelowPos d (by linarith))
        (by
          apply concaveIccSubset (f := sin) (l2 := 0) (r2 := Real.pi) concaveOn_sin_Icc
          · simp [Icc]
            intros a h1 h2
            constructor
            · exact Preorder.le_trans 0 l a hl h1
            · exact le_trans h2 hu
        )
        (by simp; linarith)
        (by simp; linarith)

theorem arithTransSineApproxBelowPos' (d : ℕ) (t lb ub evalL evalU : ℝ) (hl : 0 ≤ lb) (hu : ub ≤ Real.pi)
    (hl' : evalL = taylorWithinEval Real.sin d Set.univ 0 lb - (lb ^ (d + 1) / (d + 1).factorial))
    (hu' : evalU = taylorWithinEval Real.sin d Set.univ 0 ub - (ub ^ (d + 1) / (d + 1).factorial)) :
    (t ≥ lb ∧ t ≤ ub) → sin t ≥ evalL + ((evalL - evalU) / (lb - ub)) * (t - lb) := by
  rw [add_comm]
  intros ht; simp only [hl', hu']

  exact ge_concave_of_ge (l := lb) (u := ub) (t := t) (p := fun x => taylorWithinEval Real.sin d Set.univ 0 x - x ^ (d + 1) / (d + 1).factorial) (f := sin) (s := Icc lb ub) ht
        (sineApproxBelowPos d hl)
        (sineApproxBelowPos d (by linarith))
        (by
          apply concaveIccSubset (f := sin) (l2 := 0) (r2 := Real.pi) concaveOn_sin_Icc
          · simp [Icc]
            intros a h1 h2
            constructor
            · exact Preorder.le_trans 0 lb a hl h1
            · exact le_trans h2 hu
        )
        (by simp; linarith)
        (by simp; linarith)

theorem arithTransSineApproxBelowPosComp (d : ℕ) (t lb ub evalL evalU : ℝ) (hl : 0 ≤ lb) (hu : ub ≤ Real.pi)
    (hl' : evalL = sinTaylor d lb - (lb ^ (d + 1) / (d + 1).factorial))
    (hu' : evalU = sinTaylor d ub - (ub ^ (d + 1) / (d + 1).factorial)) :
    (t ≥ lb ∧ t ≤ ub) → sin t ≥ evalL + ((evalL - evalU) / (lb - ub)) * (t - lb) := by
  rw [<- sinEmbedding] at hl'
  rw [<- sinEmbedding] at hu'
  exact fun a => arithTransSineApproxBelowPos' d t lb ub evalL evalU hl hu hl' hu' a

end Smt.Reconstruct.Real.TransFns
