/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Data.Real.Basic

namespace Smt.Reconstruct.Arith

instance lorInt : LinearOrderedRing Int := inferInstance
noncomputable instance lorReal : LinearOrderedRing Real := inferInstance

end Smt.Reconstruct.Arith
