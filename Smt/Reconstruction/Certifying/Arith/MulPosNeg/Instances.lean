import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Algebra.Order.Ring.Lemmas

instance lorInt : LinearOrderedRing Int := inferInstance
instance lorRat : LinearOrderedRing Rat := inferInstance
