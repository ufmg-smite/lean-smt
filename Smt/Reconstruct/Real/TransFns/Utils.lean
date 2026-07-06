/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Tactic

open scoped Nat

open Set Real

namespace Smt.Reconstruct.Real

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
  · simp
  · simp [ih.2, iteratedDeriv_succ']
    have :=  Nat.mod_lt n (show 4 > 0 by decide)
    interval_cases hn : n % 4
      <;> simp [hn, Nat.add_mod]
      <;> ext
      <;> have : (fun x => (-sin x)) = -Real.sin := rfl
      <;> simp [this, iteratedDeriv_neg, ih]

theorem iteratedDerivWithin_eq_iteratedDeriv {f : Real → Real} (hf : ContDiff Real (⊤ : ℕ∞) f) (hs : UniqueDiffOn Real s):
  ∀ x ∈ s, iteratedDerivWithin d f s x = iteratedDeriv d f x := by
  induction' d with d hd
  · simp
  · intro x hx
    rw [iteratedDerivWithin_succ, iteratedDeriv_succ, derivWithin, deriv]
    rw [fderivWithin_congr hd (hd x hx)]
    rw [fderivWithin_eq_fderiv (UniqueDiffOn.uniqueDiffWithinAt hs hx)]
    apply Differentiable.differentiableAt (ContDiff.differentiable_iteratedDeriv d hf (Batteries.compareOfLessAndEq_eq_lt.mp rfl))

theorem iteratedDerivWithin_congr {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} {s : Set 𝕜} (hs : Set.EqOn f₁ f s) (_hxs : UniqueDiffOn 𝕜 s) (hx2 : x ∈ s) : iteratedDerivWithin n f₁ s x = iteratedDerivWithin n f s x := by
  revert x
  induction' n with n hn
  <;> intro x hx2
  · have hx : f₁ x = f x := hs hx2; simp [hx]
  · simp only [iteratedDerivWithin_succ]
    simp only [Set.EqOn] at hs
    rw [derivWithin_congr (by simp [Set.EqOn]; intro y hy; exact hn hy) (hn hx2)]

theorem deriv_comp_mul {f : Real → Real} (hd : Differentiable Real f) :
    ∀ x, deriv (fun x => f (c*x)) x = c * deriv f (c*x) := by
  intro x
  rw [show (fun x => f (c*x)) = f ∘ (fun x => c*x) by rfl]
  rw [deriv_comp _ (Differentiable.differentiableAt hd) (by apply DifferentiableAt.const_mul (differentiableAt_fun_id))]
  rw [deriv_const_mul _ (differentiableAt_fun_id), mul_comm]
  simp

theorem iteratedDeriv_const_mul {f : ℝ → ℝ } (d : Nat) (c : Real) (hf : ContDiff Real (⊤ : ℕ∞) f) :
    ∀ x, iteratedDeriv d (fun x => f (c*x)) x = c^d * (iteratedDeriv d f (c*x)) := by
  induction' d with d ih
  · simp
  · intro x
    rw [iteratedDeriv_succ]
    rw [congrArg deriv (funext ih)]
    rw [deriv_const_mul, deriv_comp_mul, ← iteratedDeriv_succ, pow_succ', ← mul_assoc]
    · linarith
    · apply ContDiff.differentiable_iteratedDeriv d hf (Batteries.compareOfLessAndEq_eq_lt.mp rfl)
    · apply Differentiable.differentiableAt
      rw [show (fun x => iteratedDeriv d f (c * x)) = ((iteratedDeriv d f) ∘ (fun x => c*x)) by rfl]
      apply Differentiable.comp (ContDiff.differentiable_iteratedDeriv d hf (Batteries.compareOfLessAndEq_eq_lt.mp rfl))
      apply Differentiable.const_mul (differentiable_id)

lemma taylorCoeffWithin_neg (d _ : ℕ) (hf : ContDiff Real (⊤ : ℕ∞) f):
    taylorCoeffWithin f d Set.univ x₀ = (-1 : Real)^d * taylorCoeffWithin (fun x => f (-x)) d Set.univ (-x₀) := by
  simp only [taylorCoeffWithin]
  rw [← iteratedDerivWithin_congr (f := fun i => f (-i)) (f₁ := fun i => f (-1*i)) (by simp [Set.eqOn_refl]) uniqueDiffOn_univ (mem_univ _)]
  rw [iteratedDerivWithin_univ, iteratedDerivWithin_univ, iteratedDeriv_const_mul d _ hf]
  simp only [ mul_neg, neg_mul, one_mul, neg_neg]
  rw [mul_comm, smul_eq_mul, smul_eq_mul, mul_assoc]; congr 1
  rw [mul_comm, ← mul_assoc, ← pow_add, ← two_mul, Even.neg_one_pow (by simp), one_mul]

theorem taylorWithinEval_neg {f : Real → Real} (hf : ContDiff Real (⊤ : ℕ∞) f) :
    taylorWithinEval f n Set.univ x₀ x = taylorWithinEval (fun x => f (-x)) n Set.univ (-x₀) (-x) := by
  unfold taylorWithinEval
  unfold taylorWithin
  rw [Finset.sum_congr rfl
      (by intro d _; rw [taylorCoeffWithin_neg d n hf])]
  simp
  apply Finset.sum_congr rfl
  intro d _
  simp [← mul_pow, ← mul_assoc]
  apply Or.inl; ring

theorem derivWithin_eq_deriv {f : Real → Real} (hf : ContDiff Real ⊤ f) (hs : UniqueDiffWithinAt Real s x) :
    derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv]
  rw [fderivWithin_eq_fderiv hs (ContDiffAt.differentiableAt (ContDiff.contDiffAt hf) (by simp))]

-- This should be generalized
theorem taylorCoeffWithin_eq {f : Real → Real} (s : Set Real) (hx : x₀ ∈ s) (hs : UniqueDiffOn ℝ s) (hf : ContDiff Real (⊤ : ℕ∞) f):
    (taylorCoeffWithin f d s x₀) = (taylorCoeffWithin f d Set.univ x₀) := by
  simp only [taylorCoeffWithin]
  rw [iteratedDerivWithin_eq_iteratedDeriv hf hs _ hx, iteratedDerivWithin_univ]

-- This should be generalized
theorem taylorWithinEval_eq {f : Real → Real} (s : Set Real) (hs : x₀ ∈ s) (hs1 : UniqueDiffOn ℝ s) (hf : ContDiff Real (⊤ : ℕ∞) f) :
    (taylorWithinEval f d s x₀) = (taylorWithinEval f d Set.univ x₀) := by
  ext x
  simp only [taylorWithinEval, taylorWithin, taylorCoeffWithin_eq s hs hs1 hf]

theorem taylor_mean_remainder_lagrange₁ {f : ℝ → ℝ} {x x₀ : ℝ} (n : ℕ) (hx : x < x₀)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ x' ∈ Ioo x x₀, f x - taylorWithinEval f n (Icc x x₀) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x x₀) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have H1 : ContDiff ℝ (⊤ : ℕ∞) fun p => f (-p) := (show (f ∘ (fun x => -x)) = (fun p => f (-p)) by rfl) ▸ ContDiff.comp hf contDiff_neg
  have H2 : DifferentiableOn ℝ (iteratedDerivWithin n (fun x => f (-x)) (uIcc (-x₀) (-x))) (uIoo (-x₀) (-x)) := by
    rw [uIcc_of_le (le_of_lt (neg_lt_neg hx)), uIoo_of_lt (neg_lt_neg hx)]
    apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
    apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := n + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc (neg_lt_neg hx))
    apply ContDiff.contDiffOn ((contDiff_infty.mp H1) (n + 1))
  have ⟨x' , hx', H⟩:= taylor_mean_remainder_lagrange (f := fun x => f (-x)) (n := n) (ne_of_lt (neg_lt_neg hx)) (ContDiff.contDiffOn ((contDiff_infty.mp H1) n)) H2
  rw [uIoo_of_lt (neg_lt_neg hx)] at hx'
  rw [uIcc_of_le (le_of_lt (neg_lt_neg hx))] at H
  have hx'' : -x' ∈ Ioo x x₀ := by
    simp at *
    apply And.intro
    <;> apply neg_lt_neg_iff.mp
    <;> simp [hx']
  use -x', hx''
  rw [neg_neg, taylorWithinEval_eq _ (by simp [le_of_lt hx]) (uniqueDiffOn_Icc (by simp [hx])) H1] at H
  rw [taylorWithinEval_neg H1, ←taylorWithinEval_eq (Icc x x₀) (by simp [le_of_lt hx]) (uniqueDiffOn_Icc hx) (by simp [hf])] at H
  simp only [neg_neg, sub_neg_eq_add] at H
  rw [H, iteratedDerivWithin_eq_iteratedDeriv hf (uniqueDiffOn_Icc (by simp [hx])) _ (Set.Ioo_subset_Icc_self hx''), iteratedDerivWithin_eq_iteratedDeriv H1 (uniqueDiffOn_Icc (by simp [hx])) _ (Set.Ioo_subset_Icc_self hx')]
  rw [show (fun x => f (-x)) = (fun x => f (-1 * x)) by simp]
  rw [iteratedDeriv_const_mul _ _ hf, mul_rotate, mul_assoc, ←mul_pow, add_comm (-x) x₀]
  simp [sub_eq_add_neg]

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

theorem neg_one_le_iteratedDeriv_sin (n : Nat) (x : Real) : -1 ≤ (iteratedDeriv n sin) x := by
  have :=  Nat.mod_lt n (show 4 > 0 by decide)
  interval_cases hn : n % 4
  <;> simp [iteratedDeriv_sin_cos, hn, sin_le_one, neg_one_le_sin, cos_le_one, neg_one_le_cos]

theorem iteratedDeriv_sin_le_one (n : Nat) (x : Real) : (iteratedDeriv n sin) x ≤ 1 := by
  have :=  Nat.mod_lt n (show 4 > 0 by decide)
  interval_cases hn : n % 4
  <;> simp [iteratedDeriv_sin_cos, hn, sin_le_one, neg_one_le_sin, cos_le_one, neg_one_le_cos, neg_le]

theorem neg_one_le_iteratedDeriv_cos (n : Nat) (x : Real) : -1 ≤ (iteratedDeriv n cos) x := by
  have :=  Nat.mod_lt n (show 4 > 0 by decide)
  interval_cases hn : n % 4
  <;> simp [iteratedDeriv_sin_cos, hn, sin_le_one, neg_one_le_sin, cos_le_one, neg_one_le_cos]

theorem iteratedDeriv_cos_le_one (n : Nat) (x : Real) : (iteratedDeriv n cos) x ≤ 1 := by
  have :=  Nat.mod_lt n (show 4 > 0 by decide)
  interval_cases hn : n % 4
  <;> simp [iteratedDeriv_sin_cos, hn, sin_le_one, neg_one_le_sin, cos_le_one, neg_one_le_cos, neg_le]

end Smt.Reconstruct.Real
