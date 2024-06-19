/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Logic
import Batteries.Data.Rat

namespace Rat
protected theorem lt_iff_blt {x y : Rat} : x < y ↔ x.blt y := by
  simp only [LT.lt]

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

protected theorem add_zero : ∀ a : Rat, a + 0 = a := by
  sorry

protected theorem add_assoc : ∀ a b c : Rat, a + b + c = a + (b + c) := by
  sorry

protected theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) := by
  sorry

end Rat
