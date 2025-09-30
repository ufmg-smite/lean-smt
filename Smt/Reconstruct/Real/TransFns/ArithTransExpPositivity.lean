/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule26ARITH_TRANS_EXP_POSITIVITYE
-/

import Mathlib.Analysis.Complex.Exponential

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransExpPositivity (t : Real) : Real.exp t > 0 := Real.exp_pos t

end Smt.Reconstruct.Real.TransFns
