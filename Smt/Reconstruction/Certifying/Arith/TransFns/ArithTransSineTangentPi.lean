/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule27ARITH_TRANS_SINE_TANGENT_PIE
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

theorem arithTransSineTangentPi : ∀ (t : ℝ),
    (t > -pi → sin t > -pi - t) ∧ (t < pi → sin t < pi - t) := by
  intro t
  apply And.intro
  · intro ht; admit
  · intro ht; admit
    
