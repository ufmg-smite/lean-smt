import Smt.Reconstruction.Certifying.Arith.MulPosNeg
import Smt.Reconstruction.Certifying.Boolean

import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Parity

open Smt.Reconstruction.Certifying

mutual

theorem powEvenI : ∀ {k : Nat} {z : Int} , z < 0 → Even k → Int.pow z k > 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp
  | succ k' =>
    have k'NotEven := Nat.even_add_one.mp h₂
    have k'Odd := Nat.odd_iff_not_even.mpr k'NotEven
    have rc := powOddI h₁ k'Odd
    simp [Int.pow]
    have mulZ := arith_mul_neg_lt rc h₁
    simp at mulZ
    rw [mul_comm]
    exact mulZ

theorem powOddI : ∀ {k : Nat} {z : Int} , z < 0 → Odd k → Int.pow z k < 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp at h₂
  | succ k' =>
    simp at h₂
    have k'Even := notNotElim (mt Nat.even_add_one.mpr h₂)
    have rc := powEvenI h₁ k'Even
    simp [Int.pow]
    have mulZ := arith_mul_neg_lt rc h₁
    simp at mulZ
    rw [mul_comm]
    exact mulZ

end

mutual

theorem powEvenR : ∀ {k : Nat} {q : Rat} , q < 0 → Even k → HPow.hPow q k > 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp
  | succ k' =>
    have k'NotEven := Nat.even_add_one.mp h₂
    have k'Odd := Nat.odd_iff_not_even.mpr k'NotEven
    have rc := powOddR h₁ k'Odd
    show 0 < z * z ^ k'
    have mulQ := arith_mul_neg_lt rc h₁
    simp at mulQ
    exact mulQ

theorem powOddR : ∀ {k : Nat} {q : Rat} , q < 0 → Odd k → HPow.hPow q k < 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp at h₂
  | succ k' =>
    simp at h₂
    have k'Even := notNotElim (mt Nat.even_add_one.mpr h₂)
    have rc := powEvenR h₁ k'Even
    show 0 > z * z ^ k'
    have mulQ := arith_mul_neg_lt rc h₁
    simp at mulQ
    exact mulQ

end

theorem powPosI : ∀ {k : Nat} {z : Int} , z > 0 → z ^ k > 0 := by
  intro k z h
  cases k with
  | zero    => simp
  | succ k' =>
    have ih := @powPosI k' z h
    show z ^ k' * z > 0
    have h₂ := arith_mul_pos_lt ih h
    simp at h₂
    rw [mul_comm]
    exact h₂

theorem powPosR : ∀ {k : Nat} {z : Rat} , z > 0 → z ^ k > 0 := by
  intro k z h
  cases k with
  | zero    => simp
  | succ k' =>
    have ih := @powPosR k' z h
    show z * z ^ k' > 0
    have h₂ := arith_mul_pos_lt ih h
    simp at h₂
    exact h₂

variable {α : Type}

variable [LinearOrderedRing α]

variable {a b : α}

theorem combineSigns₁ : a > 0 → b > 0 → b * a > 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combineSigns₂ : a > 0 → b < 0 → b * a < 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_right h₂ h₁
  simp at h
  exact h

theorem combineSigns₃ : a < 0 → b > 0 → b * a < 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combineSigns₄ : a < 0 → b < 0 → b * a > 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_neg_left h₁ h₂
  simp at h
  exact h

theorem castPos : ∀ (a : Int), a > 0 → Rat.ofInt a > 0 := by
  intros a h
  simp [h]

theorem castNeg : ∀ (a : Int), a < 0 → Rat.ofInt a < 0 := by
  intros a h
  simp [h]

instance : HMul ℤ ℚ ℚ where
  hMul z q := Rat.ofInt z * q

instance : HMul ℚ ℤ ℚ where
  hMul q z := q * Rat.ofInt z
