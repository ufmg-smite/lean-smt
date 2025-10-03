/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- Implementation of rules about transcendental functions from cvc5

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAboveNeg
import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAbovePos
import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxBelow
import Smt.Reconstruct.Real.TransFns.ArithTransExpNeg
import Smt.Reconstruct.Real.TransFns.ArithTransExpPositivity
import Smt.Reconstruct.Real.TransFns.ArithTransExpSuperLin
import Smt.Reconstruct.Real.TransFns.ArithTransExpZero
import Smt.Reconstruct.Real.TransFns.ArithTransPi
import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxAboveNeg
import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxAbovePos
import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowNeg
import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowPos
import Smt.Reconstruct.Real.TransFns.ArithTransSineBounds
import Smt.Reconstruct.Real.TransFns.ArithTransSineShift
import Smt.Reconstruct.Real.TransFns.ArithTransSineSymmetry
import Smt.Reconstruct.Real.TransFns.ArithTransSineTangentPi
import Smt.Reconstruct.Real.TransFns.ArithTransSineTangentZero
import Smt.Reconstruct.Real.TransFns.TaylorComp
