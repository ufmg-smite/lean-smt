/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule25ARITH_TRANS_SINE_SYMMETRYE
-/

import Mathlib.Analysis.Complex.Trigonometric

open Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineSymmetry : ∀ (t : ℝ), sin t + sin (- t) = 0 := by
  intro t
  rw [sin_neg]
  simp

end Smt.Reconstruct.Real.TransFns
