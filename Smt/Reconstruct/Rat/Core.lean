/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Data.Rat

namespace Rat

def abs (x : Rat) := if x < 0 then -x else x

protected theorem add_zero : ∀ a : Rat, a + 0 = a := by
  sorry

protected theorem add_assoc : ∀ a b c : Rat, a + b + c = a + (b + c) := by
  sorry

protected theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) := by
  sorry

end Rat
