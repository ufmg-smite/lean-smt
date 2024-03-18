/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule25ARITH_TRANS_EXP_SUPER_LINE
-/

import Mathlib.Data.Complex.Exponential

import Smt.Reconstruct.Prop

namespace Smt.Reconstruct.Arith

open Smt.Reconstruct.Prop

theorem arithTransExpSuperLin' (t : ℝ) (ht : t > 0) :
    Real.exp t > t + 1 :=
  Real.add_one_lt_exp (ne_of_gt ht)

theorem arithTransExpSuperLin (t : ℝ) :
    t ≤ 0 ∨ Real.exp t > t + 1 := by
  apply orImplies
  intro h
  simp at h
  exact arithTransExpSuperLin' t h

end Smt.Reconstruct.Arith
