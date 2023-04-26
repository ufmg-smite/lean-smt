import Smt.Reconstruction.Certifying.Arith.MulPosNeg
import Smt.Reconstruction.Certifying.Boolean

import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Parity

open Smt.Reconstruction.Certifying

#check Nat.odd_iff

mutual

theorem powEven : ∀ {k : Nat} {z : Int} , z < 0 → Even k → Int.pow z k > 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp
  | succ k' =>
    have k'NotEven := Nat.even_add_one.mp h₂
    have k'Odd := Nat.odd_iff_not_even.mpr k'NotEven
    have rc := powOdd h₁ k'Odd
    simp [Int.pow]
    have mulZ := arith_mul_neg_lt rc h₁
    simp at mulZ
    rw [mul_comm]
    exact mulZ

theorem powOdd : ∀ {k : Nat} {z : Int} , z < 0 → Odd k → Int.pow z k < 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp at h₂
  | succ k' =>
    simp at h₂
    have k'Even := notNotElim (mt Nat.even_add_one.mpr h₂)
    have rc := powEven h₁ k'Even
    simp [Int.pow]
    have mulZ := arith_mul_neg_lt rc h₁
    simp at mulZ
    rw [mul_comm]
    exact mulZ

end
