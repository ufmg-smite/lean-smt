/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- implementation of rules about transcendental functions from cvc5

import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAboveNeg
import Smt.Reconstruct.Arith.TransFns.ArithTransExpNeg
import Smt.Reconstruct.Arith.TransFns.ArithTransExpPositivity
import Smt.Reconstruct.Arith.TransFns.ArithTransExpSuperLin
import Smt.Reconstruct.Arith.TransFns.ArithTransExpZero
import Smt.Reconstruct.Arith.TransFns.ArithTransPi
import Smt.Reconstruct.Arith.TransFns.ArithTransSineBounds
import Smt.Reconstruct.Arith.TransFns.ArithTransSineSymmetry
import Smt.Reconstruct.Arith.TransFns.ArithTransSineTangentPi
import Smt.Reconstruct.Arith.TransFns.ArithTransSineTangentZero
