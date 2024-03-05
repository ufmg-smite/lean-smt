/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- implementation of:
-- https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule14ARITH_MULT_POSE
-- and
-- https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule14ARITH_MULT_NEGE

import Smt.Reconstruct.Arith.MulPosNeg.Lemmas
import Smt.Reconstruct.Arith.MulPosNeg.Tactic
