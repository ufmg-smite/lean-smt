import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Init.Function
import Mathlib.Data.Rat.Order

open Function

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

instance : CovariantClass Rat Rat (· + ·) (· < ·) where
  elim := by
    intros a b c h
    exact add_lt_add_left h a

#check mul_lt_mul_left'

instance : CovariantClass Rat Rat (swap (· + ·)) (· < ·) where
  elim := by
    intros a b c h
    exact add_lt_add_right h a
  
instance : CovariantClass Rat Rat (· + ·) (· ≤ ·) where
  elim := by
    intros a b c h
    exact add_le_add_left h a

instance : CovariantClass Rat Rat (swap (· + ·)) (· ≤ ·) where
  elim := by
    intros a b c h
    exact add_le_add_right h a
