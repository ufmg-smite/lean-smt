/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_NEGE
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Smt.Reconstruct.Arith

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
  have o : Set.Ioo l r ⊆ Set.Icc l r := Set.Ioo_subset_Icc_self
  exact DifferentiableOn.mono h' o

-- If you need a theorem for expSeries, use this: Real.exp_eq_exp_ℝ
-- Coming back to Real.exp because taylorWithinEval is the way of taking taylor polynomial used by taylor's theorem
-- Assuming strict bounds for now. After this, prove for t = l and t = r
-- need to add a hypothesis stating that there is no inflection point
-- between l and r for p
-- and also that p is convex at l
-- and also that t < 0
-- theorem arithTransExpApproxAboveNeg (d : ℕ) (l u t : ℝ) :
--     let p: ℝ → ℝ := taylorWithinEval Real.exp d (Set.Ioo l u) 0
--     let secant := ((p l - p u) / (l - u)) * (t - l) + p l
--     StrictConvexOn ℝ (Set.Icc l u) p → t < 0 → t > l ∧ t < u → Real.exp t ≤ secant := by
--   rintro p secant p_conv t_neg ⟨l_bound, u_bound⟩
--   have lLeT : l ≤ t := LT.lt.le l_bound
--   have tLeU : t ≤ u := LT.lt.le u_bound
--   have lLeU : l ≤ u := LE.le.trans lLeT tLeU
--   have lLtU : l < u := LT.lt.trans l_bound u_bound
--   /- have taylor := taylor_mean_remainder_lagrange (f := -Real.exp) (x := -t) (x₀ := 0) -/
--   /-   (hx := neg_pos.mpr t_neg) (hf := exp_contDiffOn d l t) () (hf' := exp_DiffOn d l t l_bound) -/
--   have conv_imples: (p l - p t) / (l - t) < (p u - p t) / (u - t) :=
--     StrictConvexOn.secant_strict_mono p_conv (a := t) (x := l) (y := u)
--       (Set.mem_Icc.mpr ⟨lLeT, tLeU⟩)
--       (Set.left_mem_Icc.mpr lLeU)
--       (Set.right_mem_Icc.mpr lLeU)
--       (ne_of_lt l_bound) (Ne.symm (ne_of_lt u_bound)) lLtU
--   simp
--   admit

/- example (x : ℝ) : x < 0 → -x > 0 := by intro h; library_search -/


/- #check Convex -/
/- example : StrictConvexOn ℝ  (Set.Icc 1 2) Real.exp := by -/
/-   simp [StrictConvexOn] -/
/-   apply And.intro -/
/-   · admit -/
/-   · admit -/

end Smt.Reconstruct.Arith
