/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule28ARITH_TRANS_EXP_APPROX_BELOWE
-/

import Smt.Reconstruct.Real.TransFns.Utils
import Smt.Reconstruct.Real.TransFns.TaylorComp

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem DifferentiableOn_iteratedDerivWithin {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hx : a < b) :
    DifferentiableOn ℝ (iteratedDerivWithin d f (Icc a b)) (Ioo a b) := by
    apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
    apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
    apply ContDiff.contDiffOn (by apply ContDiff.of_le hf (by norm_cast; simp))

-- can definitely be shortened. same proof below
theorem arithTransExpApproxBelow₁ (x : ℝ) (d n : ℕ) (_ : d = 2 * n + 1) (hx : 0 < x) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have h2 : DifferentiableOn ℝ (iteratedDerivWithin d rexp (Icc 0 x)) (Ioo 0 x) := by
        apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
        apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
        apply ContDiff.contDiffOn ((contDiff_infty.mp contDiff_exp) _)
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange hx (ContDiff.contDiffOn (s := Icc 0 x) (n := d) contDiff_exp) h2
    rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x')) (by simp [le_of_lt hx])

-- see the last line. this probably holds for any function.
theorem arithTransExpApproxBelow₂ (x : ℝ) (d n : ℕ) (h : d = 2 * n + 1) (hx : x < 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ hx contDiff_exp (n := d)
    rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x'))
    apply Even.pow_nonneg; rw [h, show 2*n + 1 + 1 = 2*(n+1) by ring]; simp

theorem arithTransExpApproxBelow₃ (x : ℝ) (d n : ℕ) (_ : d = 2 * n + 1) (hx : x = 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
  rw [hx]
  simp

lemma deriv_taylor (d : ℕ) : deriv (taylorWithinEval Real.exp (d + 1) Set.univ 0) = taylorWithinEval Real.exp d Set.univ 0 := by
  rw [ext_taylor_exp_eq, ext_taylor_exp_eq]
  ext x
  have : (fun x : Real => ∑ i ∈ Finset.range (d + 1 + 1), x ^ i / ↑i.factorial) = ∑ i ∈ Finset.range (d + 1 + 1), (fun x : Real => x ^ i / ↑i.factorial) := by bound
  rw [this, deriv_sum]
  · simp
    induction d
    next => simp [Finset.range]
    next d IH =>
      rw [Finset.sum_range_succ, IH]
      rw [Finset.sum_range_succ (n := d + 1)]
      simp
      field_simp
      rw [mul_comm, <- mul_assoc]
      have : ((d + 1).factorial : Real) * (d + 2) = (d + 2).factorial := by
        norm_cast
        simp [Nat.factorial]
        linarith
      rw [this]
      · linarith
      · bound
  · intros i hi
    have : i.factorial ≠ 0 := Nat.factorial_ne_zero i
    have : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr this
    bound

theorem expApproxAbove {x : Real} (d k : Nat) (hd : d = 2*k) (hx: x < 0) :
  Real.exp x ≤ taylorWithinEval Real.exp d Set.univ 0 x := by
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ hx contDiff_exp (n := d)
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
  rw [←sub_nonpos, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
  apply mul_nonpos_of_nonpos_of_nonneg _ (by apply inv_nonneg.mpr; simp)
  apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos x'))
  apply Odd.pow_nonpos _ (by simp[le_of_lt hx]); simp [hd]

theorem taylorWithin_mono : ∀ (d : Nat), Odd d → Monotone (taylorWithinEval Real.exp d Set.univ 0) := by
  intros d hd
  apply monotone_of_deriv_nonneg
  · rw [ext_taylor_exp_eq]
    have : (fun x : Real => ∑ i ∈ Finset.range (d + 1), x ^ i / ↑i.factorial) = ∑ i ∈ Finset.range (d + 1), (fun x : Real => x ^ i / ↑i.factorial) := by bound
    rw [this]
    refine Differentiable.sum ?_
    intros i hi
    have h1 : i.factorial ≠ 0 := Nat.factorial_ne_zero i
    have h2 : (i.factorial : Real) ≠ 0 := Nat.cast_ne_zero.mpr h1
    refine Differentiable.div ?_ ?_ fun x => h2
    · exact differentiable_pow i
    · simp
  · intro x
    have hd_copy := hd
    obtain ⟨m, hm⟩ := hd
    obtain ⟨d', hd'⟩  : ∃ d' : Nat, d = d' + 1 := Exists.imp' (HMul.hMul 2) (fun _ a => a) hd_copy
    obtain ⟨m', hm'⟩  : Even d' := by use m; linarith
    rw [hd', deriv_taylor, hm', show m' + m' = 2 * m' by omega]
    if hx: 0 ≤ x then
      rw [taylor_exp_eq]
      positivity
    else
      push_neg at hx
      have h1 := expApproxAbove (2 * m') m' rfl hx
      have h2 : 0 ≤ Real.exp x := exp_nonneg x
      exact Preorder.le_trans 0 (rexp x) (taylorWithinEval rexp (2 * m') univ 0 x) h2 h1

theorem arithTransExpApproxBelow (t c : ℝ) (d n : ℕ) (h : d = 2 * n + 1 := by linarith) :
    t ≥ c → Real.exp t ≥ taylorWithinEval Real.exp d Set.univ 0 c := by
  intro ht
  have foo :=
    if hx : t < 0 then by
      exact arithTransExpApproxBelow₂ t d n h hx
    else if hx2 : t = 0 then by
      exact arithTransExpApproxBelow₃ t d n h hx2
    else by
      have : 0 < t := by push_neg at *; exact lt_of_le_of_ne hx (Ne.symm hx2)
      exact arithTransExpApproxBelow₁ t d n h this
  have : taylorWithinEval Real.exp d Set.univ 0 t ≥ taylorWithinEval Real.exp d Set.univ 0 c := taylorWithin_mono d (by exists n) ht
  exact Preorder.le_trans (taylorWithinEval rexp d univ 0 c) (taylorWithinEval rexp d univ 0 t) (rexp t) this foo

theorem arithTransExpApproxBelow' (t : ℝ) (c : ℝ) (w : ℝ) (d n : ℕ) (hw : taylorWithinEval Real.exp d Set.univ 0 c = w) (h : d = 2 * n + 1) :
    t ≥ c → Real.exp t ≥ w := by
      intros ht
      rw [<- hw]
      exact arithTransExpApproxBelow t c d n h ht

theorem arithTransExpApproxBelowComp (t : ℝ) (c : ℝ) (w : ℝ) (d n : ℕ) (hw : expTaylor d c = w) (h : d = 2 * n + 1) :
    t ≥ c → Real.exp t ≥ w := by
      rw [<- expEmbedding] at hw
      exact fun a => arithTransExpApproxBelow' t c w d n hw h a

end Smt.Reconstruct.Real.TransFns
