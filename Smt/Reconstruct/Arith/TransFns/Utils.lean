/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

namespace Smt.Reconstruct.Arith

open Set Real

theorem concaveOn_sin_Icc : ConcaveOn ℝ (Icc 0 π) sin := StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc

theorem strictConvexOn_sin_Icc : StrictConvexOn ℝ (Icc (- π) 0) sin := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp only [mem_Ioo] at hx
  simp
  have ⟨hx₁, hx₂⟩ := hx
  exact Real.sin_neg_of_neg_of_neg_pi_lt hx₂ hx₁

theorem convexOn_sin_Icc : ConvexOn ℝ (Icc (- π) 0) sin := StrictConvexOn.convexOn strictConvexOn_sin_Icc

theorem iteratedDeriv_sin_cos (n : Nat) :
  (iteratedDeriv n sin =
    if n % 4 = 0 then sin else
    if n % 4 = 1 then cos else
    if n % 4 = 2 then -sin else
    -cos) ∧
    (iteratedDeriv n cos =
    if n % 4 = 0 then cos else
    if n % 4 = 1 then -sin else
    if n % 4 = 2 then -cos else
    sin) := by
  induction' n with n ih
  · simp [iteratedDeriv]
  · simp [ih.1, ih.2, iteratedDeriv_succ']
    have :=  Nat.mod_lt n (show 4 > 0 by decide)
    interval_cases hn : n % 4
    <;> simp [hn, Nat.add_mod]
    <;> ext
    <;> simp [iteratedDeriv_neg, ih]

theorem DifferentiableOn_iteratedDerivWithin {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hx : a < b) :
    DifferentiableOn ℝ (iteratedDerivWithin d f (Icc a b)) (Ioo a b) := by
    apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
    apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
    apply ContDiff.contDiffOn (by apply ContDiff.of_le hf (by norm_cast; simp))

