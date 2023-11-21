import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Data.Real.Basic

instance lorInt : LinearOrderedRing Int := inferInstance
noncomputable instance lorReal : LinearOrderedRing Real := inferInstance
