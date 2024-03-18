/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Real.Archimedean

import Smt.Reconstruct.Arith.MulPosNeg.Lemmas

namespace Smt.Reconstruct.Arith

variable {α : Type} [LinearOrderedRing α] [FloorRing α]

theorem Real.neg_lt_neg {a b : α} (h : a < b) : -a > -b := by
  simp
  exact h

theorem Real.neg_le_neg {a b : α} (h : a ≤ b) : -a ≥ -b := by
  simp
  exact h

theorem castLE' : ∀ {a b : Int}, a ≤ b → (a : α) ≤ b := by simp

theorem intTightLb' : ∀ {i : Int} {c : α}, i > c → i ≥ ⌊c⌋ + 1 := by
  intros i c h
  cases lt_trichotomy i (⌊c⌋ + 1) with
  | inl iltc =>
    have ilec := (Int.lt_iff_add_one_le i (⌊c⌋ + 1)).mp iltc
    simp at ilec
    have c_le_floor := Int.floor_le c
    have cast_ilec := le_trans (castLE' ilec) c_le_floor
    have abs := lt_of_le_of_lt cast_ilec h
    simp at abs
  | inr h' => cases h' with
              | inl ieqc => exact le_of_eq (Eq.symm ieqc)
              | inr igtc => exact le_of_lt igtc

theorem intTightUb' : ∀ {i : Int} {c : α}, i < c → i ≤ ⌈c⌉ - 1 := by
  intros i c h
  have neg_c_lt_neg_i := Real.neg_lt_neg h
  have i_le_floor_neg_c: -i ≥ ⌊-c⌋ + 1 :=  by
    apply intTightLb'
    norm_cast at neg_c_lt_neg_i
  rw [Int.floor_neg] at i_le_floor_neg_c
  have i_plus_one_le_c := Int.neg_le_neg i_le_floor_neg_c
  simp at i_plus_one_le_c
  rw [add_comm] at i_plus_one_le_c
  have pf: i + 1 - 1 ≤ ⌈c⌉ - 1 := Int.add_le_add i_plus_one_le_c le_rfl
  simp at pf
  exact pf

end Smt.Reconstruct.Arith
