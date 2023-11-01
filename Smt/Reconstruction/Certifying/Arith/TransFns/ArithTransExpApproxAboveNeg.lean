/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- implementation of:
-- https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_NEGE
import Mathlib

variable (d : ℕ)
variable (l r : ℝ)

theorem exp_contDiffOn : ContDiffOn ℝ d rexp (Set.Icc l r) := by
  apply ContDiff.contDiffOn
  exact Real.contDiff_exp

theorem exp_Diff : DifferentiableOn ℝ rexp (Set.Icc l r) :=
  DifferentiableOn.exp (f := id) (s := Set.Icc l r) (by exact differentiableOn_id)

theorem exp_eq_iteratedDeriv : ∀ n x, iteratedDeriv n rexp x = rexp x := by
  intros n x
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

#check iteratedDerivWithin_univ

theorem exp_eq_iteratedDerivWithin : ∀ n x s, iteratedDerivWithin n rexp s x = rexp x := by
  intros n x s
  rw [iteratedDerivWithin, iteratedFDerivWithin]
  simp
  have h := exp_eq_iteratedDeriv n x
  rw [← h]
  rw [iteratedDeriv, iteratedFDeriv]
  simp
  admit
  

-- I am using expSeries instead of rexp because it allows me to take partial sums
-- can I use it with taylor's theorem? Yes!
-- Probably will be a good idea to change the other rules to use expSeries instead of rexp as well
-- doesnt really matter, we can use this: Real.exp_eq_exp_ℝ
-- Coming back to rexp because taylorWithinEval is the way of taking taylor polynomial used by taylor's theorem
-- Assuming strict bounds for now
theorem arithTransExpApproxAboveNeg (d : ℕ) (l u t : ℝ) :
    let p: ℝ → ℝ := taylorWithinEval rexp d (Set.Ioo l u) 0
    let secant := ((p l - p u) / (l - u)) * (t - l) + p l
    t > l ∧ t < u → rexp t ≤ secant := by
  rintro p secant ⟨l_bound, u_bound⟩ 
  simp
  have taylor := taylor_mean_remainder_lagrange (f := rexp) (x := t) (x₀ := l)
    (hx := l_bound) (hf := exp_contDiffOn d l t) (hf' := by admit)

  sorry
  /- library_search -/


