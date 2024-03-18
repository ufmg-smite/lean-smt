/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule19ARITH_TRANS_EXP_NEGE
-/

import Mathlib.Data.Complex.Exponential

namespace Smt.Reconstruct.Arith

theorem arithTransExpNeg (t : ℝ) : t < 0 ↔ Real.exp t < 1 :=
  Iff.comm.mp Real.exp_lt_one_iff

end Smt.Reconstruct.Arith
