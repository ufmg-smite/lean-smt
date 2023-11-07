/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- implementation of:
-- https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_NEGE
import Mathlib

theorem exp_contDiffOn : ∀ (d : ℕ) (l r : ℝ),
    ContDiffOn ℝ d Real.exp (Set.Icc l r) := by
  intros d l r
  apply ContDiff.contDiffOn
  exact Real.contDiff_exp

theorem t2 : ∀ (l r : ℝ), l < r → UniqueDiffOn ℝ (Set.Icc l r) := by
  intros l r h
  refine uniqueDiffOn_Icc ?hab
  exact h

theorem t1 : ∀ (n : ℕ) (l r : ℝ), ContDiffOn ℝ n Real.exp (Set.Icc l r) := by
  intros n l r
  exact exp_contDiffOn n l r

theorem exp_DiffOn : ∀ (d : ℕ) (l r : ℝ), l < r →
    DifferentiableOn ℝ (iteratedDerivWithin d Real.exp (Set.Icc l r)) (Set.Ioo l r) := by
  intros d l r h
  have d_lt_succ_d := Nat.lt.base d
  have h' := ContDiffOn.differentiableOn_iteratedDerivWithin (m := d) (n := d + 1) (t1 (d + 1) l r) (StrictMono.imp Nat.strictMono_cast d_lt_succ_d) (t2 l r h)
  have o : Set.Ioo l r ⊆ Set.Icc l r := by exact Set.Ioo_subset_Icc_self
  exact DifferentiableOn.mono h' o
  
-- If you need a theorem for expSeries, use use this: Real.exp_eq_exp_ℝ
-- Coming back to Real.exp because taylorWithinEval is the way of taking taylor polynomial used by taylor's theorem
-- Assuming strict bounds for now
theorem arithTransExpApproxAboveNeg (d : ℕ) (l u t : ℝ) :
    let p: ℝ → ℝ := taylorWithinEval Real.exp d (Set.Ioo l u) 0
    let secant := ((p l - p u) / (l - u)) * (t - l) + p l
    t > l ∧ t < u → Real.exp t ≤ secant := by
  rintro p secant ⟨l_bound, u_bound⟩ 
  have taylor := taylor_mean_remainder_lagrange (f := Real.exp) (x := t) (x₀ := l)
    (hx := l_bound) (hf := exp_contDiffOn d l t) (hf' := exp_DiffOn d l t l_bound)
  simp
  admit

