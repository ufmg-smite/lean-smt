/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule22ARITH_TRANS_SINE_SHIFTE
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.StarOrdered

namespace Smt.Reconstruct.Arith

open Real

def norm' (x : Real) : Prop := ((-Real.pi) ≤ x) ∧ (x ≤ Real.pi)

def P (x : Real) (s : Int) (y : Real) : Prop :=
  (norm' y) ∧ (sin y = sin x) ∧ (if -Real.pi ≤ x ∧ x ≤ Real.pi then x = y else x = y + 2 * Real.pi * s)

def P2 (x : Real) (s : Int) : Prop := ∃ y , P x s y

theorem tau (x : Real) : x - Real.pi + 2 * Real.pi = x + Real.pi := by linarith

theorem two_pi_ne_zero : ¬ (2 * Real.pi = 0) := by
  intro h
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
  exact pi_ne_zero h

theorem floor_div_add_one (a b : Real) : b ≠ 0 → Int.floor (a / b) + 1 = Int.floor ((a + b) / b) := by
  intro h
  rw [<- div_add_one h]
  exact Eq.symm (Int.floor_add_one (a / b))

theorem arithTransSineShift₀ : ∀ x , ∃ s y , P x s y := fun x =>
  if h : (-Real.pi ≤ x ∧ x ≤ Real.pi) then by
    use 0, x
    simp only [P, Int.cast_zero, mul_zero, add_zero, ite_self, and_self, and_true]
    exact h
  else if h2 : (Real.pi < x) then by
    let s := Int.ceil ((x - Real.pi) / (2 * Real.pi))
    use s, x - 2 * Real.pi * s
    simp only [s]
    constructor
    · simp only [norm', neg_le_sub_iff_le_add, tsub_le_iff_right]
      constructor
      · apply (le_div_iff₀' (two_pi_pos)).mp
        have := Int.ceil_le_floor_add_one ((x - Real.pi) / (2 * Real.pi))
        apply le_trans (Int.cast_le.mpr this)
        have : Int.floor ((x - Real.pi) / (2 * Real.pi)) + 1 ≤ (x - Real.pi) / (2 * Real.pi) + 1 :=
          add_le_add_right (Int.floor_le _) 1
        simp only [Int.cast_add, Int.cast_one, ge_iff_le]
        apply le_trans this
        rw [← div_add_same two_pi_ne_zero, tau]
      · apply tsub_le_iff_left.mp
        apply (div_le_iff₀' (two_pi_pos)).mp
        exact Int.le_ceil ((x - π) / (2 * π))
    · constructor
      · rw [mul_comm, sin_sub_int_mul_two_pi x s]
      · simp only [sub_add_cancel, if_true_right, and_imp]
        intros h3 h4
        linarith
  else by
    have h3 : x < -Real.pi := by aesop
    let s := Int.floor ((x + Real.pi) / (2 * Real.pi))
    use s, x - 2 * Real.pi * s
    simp only [s]
    constructor
    · simp only [norm', neg_le_sub_iff_le_add, tsub_le_iff_right]
      constructor
      · apply (le_div_iff₀' (two_pi_pos)).mp
        exact Int.floor_le ((x + π) / (2 * π))
      · apply (tsub_le_iff_left (b := Real.pi)).mp
        apply (div_le_iff₀' (two_pi_pos)).mp
        apply le_trans (Int.le_ceil ((x - Real.pi) / (2 * Real.pi)))
        apply le_trans (Int.cast_le.mpr (Int.ceil_le_floor_add_one ((x - Real.pi) / (2 * Real.pi))))
        apply Int.cast_le.mpr
        rw [floor_div_add_one _ _ two_pi_ne_zero, tau]
    · constructor
      · rw [mul_comm, sin_sub_int_mul_two_pi x s]
      · simp only [sub_add_cancel, if_true_right, and_imp]
        intros h3 h4
        linarith

open Classical

theorem arithTransSineShift₁ : ∀ (x : Real) ,
    let s := epsilon (P2 x)
    let y := epsilon (P x s)
    P x s y :=
  fun x => epsilon_spec (epsilon_spec (arithTransSineShift₀ x))

end Smt.Reconstruct.Arith
