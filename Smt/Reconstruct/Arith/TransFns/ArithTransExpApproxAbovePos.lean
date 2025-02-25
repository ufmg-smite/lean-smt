/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_POSE
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered
import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAboveNeg
/- import Mathlib.Analysis.SpecialFunctions.Pow.Real -/

namespace Smt.Reconstruct.Arith

open Set Real Nat

-- theorem pow_lt_factorial {x : ℝ} (hx : 0 < x) :
--   x^ (4*(ceil x)^2) < Nat.factorial (4*(ceil x)^2) := by
--   have h3 : 0 < (ceil x)^2 := by simp [Nat.le_ceil x, hx]
--   have h := factorial_mul_pow_sub_le_factorial (Nat.mul_le_mul_right ((ceil x)^2) (show 2 ≤ 4 by simp))
--   have h2 := le_trans (Nat.mul_le_mul_right _ (factorial_pos _)) h
--   simp at h2
--   apply lt_of_lt_of_le _ ((Nat.cast_le).mpr h2)
--   apply lt_of_le_of_lt (Real.rpow_le_rpow (le_of_lt hx) (Nat.le_ceil x) (by simp))
--   rw [← Nat.mul_sub_right_distrib]
--   simp only [cast_mul, cast_ofNat, cast_pow, succ_sub_succ_eq_sub, tsub_zero]
--   rw [show (4 : Real) = 2*2 by norm_num, mul_assoc, Real.rpow_mul (by simp) 2]
--   rw [← Real.rpow_nat_cast _ (2 * ⌈x⌉₊ ^ 2)]; push_cast; simp only [rpow_two]
--   apply Real.rpow_lt_rpow (by simp) (by norm_cast; simp [h3]) (by norm_cast; simp [h3])

-- theorem le_div_mul (n : Nat) : n - 1 ≤ 2*(n/2) := by
--   by_cases h : n%2 = 0
--   · rw [mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]
--     exact sub_le n 1
--   · rw [Nat.mod_two_ne_zero] at h
--     rw [Nat.two_mul_odd_div_two h]

-- theorem pow_lt_factorial'' {x d : ℝ} (d : Nat) (hx : 0 < x) (hd : 2*x^2 < d) :
--   x^d < Nat.factorial d := by
--   have h := factorial_mul_pow_sub_le_factorial (Nat.mul_le_mul_right (d/2) (show 1 ≤ 2 by simp))
--   have h2 := le_trans (Nat.mul_le_mul_right _ (factorial_pos _)) h
--   rw [Nat.one_mul, one_mul, mul_comm] at h2
--   have h3 := le_trans h2 (Nat.factorial_le (Nat.div_mul_le_self d 2))
--   apply lt_of_lt_of_le _ ((Nat.cast_le).mpr h3)
--   rw [(show (d/2)*2 - d/2 = d/2 by rw [mul_two]; simp)]
--   simp only [cast_mul, cast_ofNat, cast_pow, succ_sub_succ_eq_sub, tsub_zero]
--   have h4 : x < (d/2)^(1/2) := by
--     sorry
--   apply lt_of_lt_of_le (rpow_lt_rpow sorry h4 sorry)
--   rw [← rpow_mul (by linarith), (show (1/2)*d = (d : Real)/2 by linarith)]
--   norm_cast

theorem le_self_sq (n : Nat) : n ≤ n*n := by
  exact Nat.le_mul_self n

-- theorem pow_lt_factorial' {x : Real} (hx : 0 < x) (h1 : x^d < Nat.factorial d) :
--   ∀ x' ≤ x,  x'^d < Nat.factorial d := by
--   induction' d', hd' using Nat.le_induction with h ih h1
--   · norm_cast at *
--   · norm_cast; rw [pow_add, pow_one, factorial_succ, mul_comm]; push_cast
--     have h2 : x ≤ h := by
--       apply le_trans (le_ceil x); norm_cast
--       apply le_trans _ ih
--       linarith [Nat.le_mul_self (ceil x)]
--     apply mul_lt_mul (by apply lt_of_le_of_lt h2 (by simp)) (by norm_cast at *; simp [le_of_lt h1]) (by simp [hx]) (by norm_cast; simp)

theorem expApproxAbovePos {x : Real} (hx : 0 < x) (h1 : x^(d+1) < Nat.factorial (d+1)):
  let r : ℕ → ℝ → ℝ := fun d => (fun t => (1-t^(d+1)/(d+1)!))
  let p : ℕ → ℝ → ℝ := fun d => ((taylorWithinEval Real.exp d Set.univ 0) / (r d))
  ∀ x' ≤ x, 0 < x' → Real.exp x' ≤ p d x' := by
  intro r p
  intro x1 hx1 hx2
  have h2 : 0 < 1-x1^(d + 1)/(factorial (d + 1)) := by
    apply sub_pos_of_lt
    rw [div_lt_one (by norm_cast; exact factorial_pos (d+1))]
    apply lt_of_le_of_lt (pow_le_pow_left₀ (le_of_lt hx2) hx1 _) h1
  apply tsub_nonpos.mp; norm_cast at *
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange (n := d) hx2 (ContDiff.contDiffOn (s := Icc 0 x1) contDiff_exp) (DifferentiableOn_iteratedDerivWithin (contDiff_exp) hx2)
  rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx2)) (uniqueDiffOn_Icc hx2) contDiff_exp] at H
  dsimp [p]; rw [sub_div' (hc := ne_of_gt h2), mul_sub, mul_one, sub_right_comm, H]
  rw [div_le_iff₀ h2, zero_mul, tsub_nonpos]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx2) _ (Ioo_subset_Icc_self hx')]
  rw [iteratedDeriv_exp, sub_zero, mul_div_assoc]
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (by simp [le_of_lt hx2]) (by simp))
  apply le_of_lt (exp_lt_exp.mpr (mem_Ioo.mp hx').2)

theorem arithTransExpApproxAbovePos (l u t : ℝ) (ht : l ≤ t ∧ t ≤ u)
                                    (hl : 0 < l) (hd : u^(d+1) < Nat.factorial (d+1)):
  let r : ℕ → ℝ → ℝ := fun d => (fun t => (1-t^(d+1)/(d+1)!))
  let p : ℕ → ℝ → ℝ := fun d => ((taylorWithinEval Real.exp d Set.univ 0) / (r d))
  Real.exp t ≤ ((p d l - p d u) / (l - u)) * (t - l) + p d l := by
  intro r _
  have h1 := expApproxAbovePos (lt_of_lt_of_le hl (le_trans ht.1 ht.2)) hd
  apply le_convex_of_le ht (h1 l (le_trans ht.1 ht.2) hl) (h1 u (by simp) (by linarith)) convexOn_exp (Set.mem_univ _) (Set.mem_univ _)

