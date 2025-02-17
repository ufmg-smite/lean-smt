/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

import Mathlib

import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAboveNeg
import Smt.Reconstruct.Arith.TransFns.ArithTransApproxAboveBelow
import Smt.Reconstruct.Arith.TransFns.Utils

namespace Smt.Reconstruct.Arith

open Set Real

theorem concaveIccSubset {f : ℝ → ℝ} {l1 r1 l2 r2 : ℝ} : ConcaveOn ℝ (Icc l2 r2) f → Icc l1 r1 ⊆ Icc l2 r2 → ConcaveOn ℝ (Icc l1 r1) f := by
  intros h1 h2
  exact ConcaveOn.subset h1 h2 (convex_Icc l1 r1)

theorem sineApproxBelowPos {x : ℝ} (d k : Nat) (hd : d = 4*k + 3) (hx : 0 < x) (hx2 : x ≤ π):
  let p : ℕ → ℝ → ℝ := fun d => taylorWithinEval Real.sin d Set.univ 0
  p d x ≤ sin x := by
  intro p
  have : p d = taylorWithinEval Real.sin d Set.univ 0 := rfl
  rw [this]
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange (n := d) hx (ContDiff.contDiffOn contDiff_sin) (DifferentiableOn_iteratedDerivWithin contDiff_sin hx)
  have : taylorWithinEval sin d (Icc 0 x) 0 = taylorWithinEval sin d Set.univ 0 := by
    apply taylorWithinEval_eq
    · simp; exact le_of_lt hx
    · exact uniqueDiffOn_Icc hx
    · exact contDiff_sin
  rw [this] at H
  rw [←sub_nonpos]
  apply neg_le_neg_iff.mp
  rw [neg_sub, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  have : (d+1)%4 = 0 := by simp [hd, Nat.add_mod]
  simp only [this, iteratedDeriv_sin_cos, reduceIte, three_ne_zero, sub_zero, show 3 ≠ 1 by decide, show 3 ≠ 0 by decide, show 3 ≠ 2 by decide, neg_zero]
  apply mul_nonneg _ _
  · apply mul_nonneg _ _
    · simp at hx'; have ⟨hx'₁, hx'₂⟩ := hx';  apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact le_of_lt hx'₁
      · exact le_of_lt (lt_of_lt_of_le hx'₂ hx2)
    · exact le_of_lt (pow_pos hx (d + 1))
  · have := Nat.factorial_pos (d + 1); simp [this]


theorem ge_of_ConcaveOn (f : ℝ → ℝ) (hf : ConcaveOn Real s f) (hx : x ∈ s) (hz : z ∈ s)
                        (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxz : x ≤ z):
    f (t*x + (1-t)*z) ≥ t*(f x) + (1-t)*(f z) := by
  have : ConvexOn Real s (-f) := neg_convexOn_iff.mpr hf
  have := le_of_ConvexOn (-f) this hx hz ht0 ht1 hxz
  simp_all
  linarith

theorem ge_concave_of_ge {l u t : ℝ} {f p : ℝ → ℝ} (ht : l ≤ t ∧ t ≤ u) (hl : p l ≤ f l) (hu : p u ≤ f u) (hf : ConcaveOn Real s f) (hl1 : l ∈ s) (hu1 : u ∈ s) :
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
  · simp [hlu, hl, hu, (show t = u by linarith)]
    linarith

theorem arithTransSineApproxBelowPos (d k : ℕ) (hd : d = 4 * k + 3) (t l u : ℝ) (ht : l ≤ t ∧ t ≤ u)
    (hl : 0 < l) (hu : u ≤ Real.pi) :
    let p : ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
    sin t ≥ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.sin d Set.univ 0 x := fun _ => rfl

  exact ge_concave_of_ge (l := l) (u := u) (t := t) (p := p) (f := sin) (s := Icc l u) ht
        (by rw [hp]; exact sineApproxBelowPos d k hd hl (by linarith))
        (by rw [hp]; exact sineApproxBelowPos d k hd (by linarith) hu)
        (by
          apply concaveIccSubset (f := sin) (l2 := 0) (r2 := Real.pi) concaveOn_sin_Icc
          · simp [Icc]
            intros a h1 h2
            constructor
            · exact le_of_lt (lt_of_lt_of_le hl h1)
            · exact le_trans h2 hu
        )
        (by simp; linarith)
        (by simp; linarith)

end Smt.Reconstruct.Arith
