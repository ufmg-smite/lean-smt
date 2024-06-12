/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Real.Basic

namespace Smt.Reconstruct.Arith

variable {α : Type}

variable [LinearOrderedRing α]

variable {a b c : α}

@[simp] def zToR (i : Int) : Real := ↑i

def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ ht₁, ht₂ ⟩ := h₂
  exact h₁ ht₁ ht₂

theorem arith_mul_pos_lt : c > 0 ∧ a < b → c * a < c * b :=
  uncurry (flip mul_lt_mul_of_pos_left)

theorem arith_mul_pos_le : c > 0 ∧ a ≤ b → c * a ≤ c * b := λ h =>
  mul_le_mul_of_nonneg_left h.2 (le_of_lt h.1)

theorem arith_mul_pos_gt : c > 0 ∧ a > b → c * a > c * b := arith_mul_pos_lt

theorem arith_mul_pos_ge : c > 0 ∧ a ≥ b → c * a ≥ c * b := arith_mul_pos_le

theorem arith_mul_pos_eq : c > 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

theorem arith_mul_neg_lt : c < 0 ∧ a < b → c * a > c * b :=
  uncurry (flip mul_lt_mul_of_neg_left)

theorem arith_mul_neg_le : c < 0 ∧ a ≤ b → c * a ≥ c * b := λ h =>
  (mul_le_mul_left_of_neg h.1).mpr h.2

theorem arith_mul_neg_gt : c < 0 ∧ a > b → c * a < c * b := arith_mul_neg_lt

theorem arith_mul_neg_ge : c < 0 ∧ a ≥ b → c * a ≤ c * b := arith_mul_neg_le

theorem arith_mul_neg_eq : c < 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

theorem castLT : ∀ {a b : Int}, a < b → zToR a < zToR b := by simp

theorem castGTZero : ∀ {a : Int}, 0 > a → 0 > zToR a := by simp

theorem castLE : ∀ {a b : Int}, a ≤ b → zToR a ≤ zToR b := by simp

theorem castGEZero : ∀ {a : Int}, a ≤ 0 → zToR a ≤ 0 := by simp

theorem castLTZero : ∀ {a : Int}, a > 0 → zToR a > 0 := by simp

theorem castLEZero : ∀ {a : Int}, a ≥ 0 → zToR a ≥ 0 := by simp

theorem castFstLT {p : Prop} {a : Int} : 0 < a ∧ p → (0 < zToR a) ∧ p :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨castLTZero h₁, h₂⟩

theorem castFstLE {p : Prop} {a : Int} : 0 ≤ a ∧ p → (0 ≤ zToR a) ∧ p :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨castLEZero h₁, h₂⟩

theorem castFstGT {p : Prop} {a : Int} : 0 > a ∧ p → (0 > zToR a) ∧ p :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨castGTZero h₁, h₂⟩

theorem castFstGE {p : Prop} {a : Int} : 0 ≥ a ∧ p → (0 ≥ zToR a) ∧ p :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨castGEZero h₁, h₂⟩

theorem castFstEQ {p : Prop} {a : Int} : (0 = a) ∧ p → (0 = zToR a) ∧ p :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨by rw [← h₁]; simp, h₂⟩

theorem castSndLT {p : Prop} {a b : Int} : p ∧ a < b → p ∧ (zToR a < zToR b) :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨h₁, castLT h₂⟩

theorem castSndLE {p : Prop} {a b : Int} : p ∧ a ≤ b → p ∧ (zToR a ≤ zToR b) :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨h₁, castLE h₂⟩

theorem castSndGT {p : Prop} {a b : Int} : p ∧ a > b → p ∧ (zToR a > zToR b) :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨h₁, castLT h₂⟩

theorem castSndGE {p : Prop} {a b : Int} : p ∧ a ≥ b → p ∧ (zToR a ≥ zToR b) :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨h₁, castLE h₂⟩

theorem castSndEQ {p : Prop} {a b : Int} : p ∧ (a = b) → p ∧ (zToR a = zToR b) :=
  by rintro ⟨h₁, h₂⟩
     exact ⟨h₁, by rw [h₂]⟩

end Smt.Reconstruct.Arith
