/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule29ARITH_TRANS_SINE_TANGENT_ZEROE
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Smt.Reconstruct.Arith

open Real

theorem sin_neg' : ∀ (t : ℝ), sin t = - sin (-t) := by
  intro t
  rw [sin_neg t]
  simp

theorem arithTransSinTangentZero : ∀ (t : ℝ),
    (t > 0 → sin t < t) ∧ (t < 0 → sin t > t) := by
  intro t
  apply And.intro
  · exact sin_lt
  · intro ht
    rw [sin_neg']
    apply lt_neg.mpr
    apply sin_lt
    linarith

end Smt.Reconstruct.Arith
