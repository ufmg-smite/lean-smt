/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Init.Function
import Mathlib.Data.Real.Basic

open Function

namespace Smt.Reconstruction.Certifying

instance : CovariantClass Nat Nat (· + ·) (· < ·) where
  elim := by
    intros a b c h
    exact Nat.add_lt_add_left h a

instance : CovariantClass Nat Nat (swap (· + ·)) (· < ·) where
  elim := by
    intros a b c h
    exact Nat.add_lt_add_right h a
  
instance : CovariantClass Nat Nat (· + ·) (· ≤ ·) where
  elim := by
    intros a b c h
    exact Nat.add_le_add_left h a

instance : CovariantClass Nat Nat (swap (· + ·)) (· ≤ ·) where
  elim := by
    intros a b c h
    exact Nat.add_le_add_right h a

instance : CovariantClass Int Int (· + ·) (· < ·) where
  elim := by
    intros a b c h
    exact Int.add_lt_add_left h a

instance : CovariantClass Int Int (swap (· + ·)) (· < ·) where
  elim := by
    intros a b c h
    exact Int.add_lt_add_right h a
  
instance : CovariantClass Int Int (· + ·) (· ≤ ·) where
  elim := by
    intros a b c h
    exact Int.add_le_add_left h a

instance : CovariantClass Int Int (swap (· + ·)) (· ≤ ·) where
  elim := by
    intros a b c h
    exact Int.add_le_add_right h a

instance : CovariantClass Real Real (· + ·) (· < ·) where
  elim := by
    intros a b c h
    exact add_lt_add_left h a

instance : CovariantClass Real Real (swap (· + ·)) (· < ·) where
  elim := by
    intros a b c h
    exact add_lt_add_right h a
  
instance : CovariantClass Real Real (· + ·) (· ≤ ·) where
  elim := by
    intros a b c h
    exact add_le_add_left h a

instance : CovariantClass Real Real (swap (· + ·)) (· ≤ ·) where
  elim := by
    intros a b c h
    exact add_le_add_right h a

end Smt.Reconstruction.Certifying
