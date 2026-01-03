/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule22ARITH_TRANS_SINE_SHIFTE
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.StarOrdered

open Real

namespace Smt.Reconstruct.Real.TransFns

def norm' (x : Real) : Prop := (-Real.pi ≤ x) ∧ (x ≤ Real.pi)

def shift_prop (x : Real) (s : Real) (y : Real) : Prop :=
  y ≥ (-1) * Real.pi ∧ y ≤ Real.pi ∧ s = ⌊s⌋ ∧ (if x ≥ (-1) * Real.pi ∧ x ≤ Real.pi then x = y else x = y + 2 * s * Real.pi) ∧ (sin y = sin x)

def shift_prop' (x : Real) (s : Real) (y : Real) : Prop :=
  (norm' y) ∧ s = ⌊s⌋ ∧ (if -Real.pi ≤ x ∧ x ≤ Real.pi then x = y else x = y + 2 * Real.pi * s) ∧ (sin y = sin x)

theorem shift_prop_shift_prop' (x : Real) (s : Real) (y : Real) :
    shift_prop x s y ↔ shift_prop' x s y := by
  simp [shift_prop, shift_prop', norm']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    constructor
    · exact And.symm ⟨h2, h1⟩
    · constructor
      · exact h3
      · constructor
        · by_cases -π ≤ x ∧ x ≤ π
          next H => simp [H] at h4 ⊢; exact h4
          next H => simp [H] at h4 ⊢; linarith
        · exact h5
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    constructor
    · exact h1
    · constructor
      · exact h2
      · constructor
        · exact h3
        · constructor
          · by_cases -π ≤ x ∧ x ≤ π
            next H => simp [H] at ⊢ h4; exact h4
            next H => simp [H] at ⊢ h4; linarith
          · exact h5

abbrev shift_prop_part (x : Real) (s : Real) : Prop := ∃ y , shift_prop x s y

theorem tau (x : Real) : x - Real.pi + 2 * Real.pi = x + Real.pi := by linarith

theorem two_pi_ne_zero : ¬ (2 * Real.pi = 0) := by
  intro h
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
  exact pi_ne_zero h

theorem floor_div_add_one (a b : Real) : b ≠ 0 → Int.floor (a / b) + 1 = Int.floor ((a + b) / b) := by
  intro h
  rw [<- div_add_one h]
  exact Eq.symm (Int.floor_add_one (a / b))

theorem arithTransSineShift₀ : ∀ x , ∃ s y , shift_prop x s y := fun x =>
  if h : (-Real.pi ≤ x ∧ x ≤ Real.pi) then by
    simp [shift_prop_shift_prop']
    use 0, x
    simp only [shift_prop', mul_zero, add_zero, ite_self, and_self, and_true]
    constructor
    · exact h
    · simp
  else if h2 : (Real.pi < x) then by
    simp [shift_prop_shift_prop']
    let s' : Int := Int.ceil ((x - Real.pi) / (2 * Real.pi))
    let s : Real := s'
    use s, x - 2 * Real.pi * s
    simp only [s]
    constructor
    · simp only [norm', neg_le_sub_iff_le_add, tsub_le_iff_right]
      constructor
      · apply (le_div_iff₀' (two_pi_pos)).mp
        have := Int.ceil_le_floor_add_one ((x - Real.pi) / (2 * Real.pi))
        apply le_trans (Int.cast_le.mpr this)
        have : Int.floor ((x - Real.pi) / (2 * Real.pi)) + 1 ≤ (x - Real.pi) / (2 * Real.pi) + 1 :=
          add_le_add_left (Int.floor_le _) 1
        simp only [Int.cast_add, Int.cast_one, ge_iff_le]
        apply le_trans this
        rw [← div_add_same two_pi_ne_zero, tau]
      · apply tsub_le_iff_left.mp
        apply (div_le_iff₀' (two_pi_pos)).mp
        exact Int.le_ceil ((x - π) / (2 * π))
    · constructor
      · unfold s'; simp
      · constructor
        · simp only [sub_add_cancel, if_true_right, and_imp]
          intros h3 h4
          linarith
        · rw [mul_comm, sin_sub_int_mul_two_pi x s']
  else by
    simp [shift_prop_shift_prop']
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
      · simp
      · constructor
        · simp only [sub_add_cancel, if_true_right, and_imp]
          intros h3 h4
          linarith
        · rw [mul_comm, sin_sub_int_mul_two_pi x s]

open Classical

theorem arithTransSineShift₁ : ∀ (x : Real),
    shift_prop x (epsilon (shift_prop_part x)) (epsilon (shift_prop x (epsilon (shift_prop_part x)))) := fun x =>
  epsilon_spec (epsilon_spec (arithTransSineShift₀ x))

end Smt.Reconstruct.Real.TransFns
