/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order

namespace Smt.Reconstruct.Arith

instance lorInt : LinearOrderedRing Int := inferInstance
instance lorRat : LinearOrderedRing Rat := inferInstance

end Smt.Reconstruct.Arith
