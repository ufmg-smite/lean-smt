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

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAboveNeg

open Set Real Nat

namespace Smt.Reconstruct.Real.TransFns

theorem le_self_sq (n : Nat) : n ≤ n*n := by
  exact Nat.le_mul_self n

theorem expApproxAbovePos {x : Real}  (h1 : x^(d+1) < Nat.factorial (d+1)):
  let r : ℕ → ℝ → ℝ := fun d => (fun t => (1-t^(d+1)/(d+1)!))
  let p : ℕ → ℝ → ℝ := fun d => ((taylorWithinEval Real.exp d Set.univ 0) / (r d))
  ∀ x' ≤ x, 0 ≤ x' → Real.exp x' ≤ p d x' := by
  intro r p x1 hx1 hx2
  cases' lt_or_eq_of_le hx2 with hx2 hx2
  · have h2 : 0 < 1-x1^(d + 1)/(factorial (d + 1)) := by
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
  · simp [← hx2, p, r]

theorem arithTransExpApproxAbovePos (l u t : ℝ) (ht : l ≤ t ∧ t ≤ u)
                                    (hl : 0 ≤ l) (hd : u^(d+1) < Nat.factorial (d+1)):
  let r : ℕ → ℝ → ℝ := fun d => (fun t => (1-t^(d+1)/(d+1)!))
  let p : ℕ → ℝ → ℝ := fun d => ((taylorWithinEval Real.exp d Set.univ 0) / (r d))
  Real.exp t ≤ ((p d l - p d u) / (l - u)) * (t - l) + p d l := by
  intro r _
  have h1 := expApproxAbovePos hd
  apply le_convex_of_le ht (h1 l (le_trans ht.1 ht.2) hl) (h1 u (by simp) (by linarith)) convexOn_exp (Set.mem_univ _) (Set.mem_univ _)

theorem arithTransExpApproxAbovePos'' (d : Nat) (l u t : ℝ) (hl : 0 ≤ l) (hd : u^(d+1) < Nat.factorial (d+1)):
  (l ≤ t ∧ t ≤ u) →
  Real.exp t ≤ (((taylorWithinEval Real.exp d Set.univ 0 l / (1-l^(d+1)/(d+1)!)) - (taylorWithinEval Real.exp d Set.univ 0 u / (1-u^(d+1)/(d+1)!))) / (l - u)) * (t - l) + (taylorWithinEval Real.exp d Set.univ 0 l) / (1-l^(d+1)/(d+1)!) := by
  intro ht
  have h1 := expApproxAbovePos hd
  apply le_convex_of_le ht (h1 l (le_trans ht.1 ht.2) hl) (h1 u (by simp) (by linarith)) convexOn_exp (Set.mem_univ _) (Set.mem_univ _)

theorem arithTransExpApproxAbovePos' (d : Nat) (l u t evalL evalU : ℝ) (hl : 0 ≤ l) (hd : u^(d+1) < Nat.factorial (d+1))
    (hl' : evalL = taylorWithinEval Real.exp d Set.univ 0 l / (1-l^(d+1)/(d+1)!))
    (hu' : evalU = taylorWithinEval Real.exp d Set.univ 0 u / (1-u^(d+1)/(d+1)!)) :
    (t ≥ l ∧ t ≤ u) → Real.exp t ≤ evalL + ((evalL - evalU) / (l - u)) * (t - l) := by
  rw [add_comm, hl', hu']
  exact arithTransExpApproxAbovePos'' d l u t hl hd

theorem arithTransExpApproxAbovePosComp (d : Nat) (l u t evalL evalU : ℝ) (hl : 0 ≤ l) (hd : u^(d+1) < Nat.factorial (d+1))
    (hl' : evalL = expTaylor d l / (1-l^(d+1)/(d+1)!))
    (hu' : evalU = expTaylor d u / (1-u^(d+1)/(d+1)!)) :
    (t ≥ l ∧ t ≤ u) → Real.exp t ≤ evalL + ((evalL - evalU) / (l - u)) * (t - l) := by
  rw [<- expEmbedding] at hl'
  rw [<- expEmbedding] at hu'
  exact fun a => arithTransExpApproxAbovePos' d l u t evalL evalU hl hd hl' hu' a

end Smt.Reconstruct.Real.TransFns
