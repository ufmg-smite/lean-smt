/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential

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

theorem iteratedDerivWithin_eq_iteratedDeriv {f : Real → Real} (hf : ContDiff Real (⊤ : ℕ∞) f) (hs : UniqueDiffOn Real s):
  ∀ x ∈ s, iteratedDerivWithin d f s x = iteratedDeriv d f x := by
  induction' d with d hd
  · simp
  · intro x hx
    rw [iteratedDerivWithin_succ (UniqueDiffOn.uniqueDiffWithinAt hs hx), iteratedDeriv_succ, derivWithin, deriv]
    rw [fderivWithin_congr hd (hd x hx)]
    rw [fderivWithin_eq_fderiv (UniqueDiffOn.uniqueDiffWithinAt hs hx)]
    apply Differentiable.differentiableAt (ContDiff.differentiable_iteratedDeriv d hf (Batteries.compareOfLessAndEq_eq_lt.mp rfl))

theorem iteratedDerivWithin_sin_eq_zero_of_even (j : ℕ) (hj : Even j) :
  iteratedDerivWithin j sin univ 0 = 0 := by
  have := Nat.mod_lt j (show 4 > 0 by decide)
  interval_cases h : j % 4
  <;> rw [← Even.mod_even_iff (show Even 4 by decide), h] at hj
  <;> try {simp only [show ¬ Even 3 by decide, Nat.not_even_one] at hj}
  <;> rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin uniqueDiffOn_univ 0 (Set.mem_univ 0)]
  <;> simp [iteratedDeriv_sin_cos, h]

theorem taylorSin_neg (x : Real) (d : Nat) :
  let p: ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
  p (-x) = -p x := by
  intro p
  simp only [p, taylor_within_apply, sub_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  cases' (Nat.even_or_odd j) with h h
  · rw [iteratedDerivWithin_sin_eq_zero_of_even j h]
    simp
  · rw [Odd.neg_pow h]
    simp
