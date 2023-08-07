/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas

import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

namespace Smt.Reconstruction.Certifying

variable {α : Type}

variable [LinearOrderedRing α]

variable {a b c : α}

variable {d e : Int}
variable {f : Rat}

def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ ht₁, ht₂ ⟩ := h₂
  exact h₁ ht₁ ht₂

theorem arith_mul_pos_lt : c > 0 ∧ a < b → c * a < c * b :=
  uncurry (flip mul_lt_mul_of_pos_left)

theorem arith_mul_pos_lt.corner : f > 0 ∧ d < e → f * d < f * e := by
  rintro ⟨h₁, h₂⟩
  have h' : (d : Rat) < e := castLT.IntRat h₂
  exact mul_lt_mul_of_pos_left h' h₁

theorem arith_mul_pos_le : c > 0 ∧ a ≤ b → c * a ≤ c * b := λ h =>
  mul_le_mul_of_nonneg_left h.2 (le_of_lt h.1)

theorem arith_mul_pos_le.corner : f > 0 ∧ d ≤ e → f * d ≤ f * e := by
  rintro ⟨ h₁, h₂ ⟩ 
  have h' : (d : Rat) ≤ e := castLE.IntRat h₂
  exact mul_le_mul_of_nonneg_left h' (le_of_lt h₁)

theorem arith_mul_pos_gt : c > 0 ∧ a > b → c * a > c * b := arith_mul_pos_lt

theorem arith_mul_pos_gt.corner : f > 0 ∧ d > e → f * d > f * e := arith_mul_pos_lt.corner

theorem arith_mul_pos_ge : c > 0 ∧ a ≥ b → c * a ≥ c * b := arith_mul_pos_le

theorem arith_mul_pos_ge.corner : f > 0 ∧ d ≥ e → f * d ≥ f * e := arith_mul_pos_le.corner

theorem arith_mul_pos_eq : c > 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

theorem arith_mul_pos_eq.corner : f > 0 ∧ d = e → f * d = f * e := by
  intros h
  rw [h.2]

theorem arith_mul_neg_lt : c < 0 ∧ a < b → c * a > c * b :=
  uncurry (flip mul_lt_mul_of_neg_left)

theorem arith_mul_neg_lt.corner : f < 0 ∧ d < e → f * d > f * e := by
  rintro ⟨h₁, h₂⟩
  have h' := castLT.IntRat h₂
  exact mul_lt_mul_of_neg_left h' h₁

theorem arith_mul_neg_le : c < 0 ∧ a ≤ b → c * a ≥ c * b := λ h =>
  (mul_le_mul_left_of_neg h.1).mpr h.2

theorem arith_mul_neg_le.corner : f < 0 ∧ d ≤ e → f * d ≥ f * e := by
  rintro ⟨h₁, h₂⟩
  have h' := castLE.IntRat h₂
  exact (mul_le_mul_left_of_neg h₁).mpr h'

theorem arith_mul_neg_gt : c < 0 ∧ a > b → c * a < c * b := arith_mul_neg_lt

theorem arith_mul_neg_gt.corner : f < 0 ∧ d > e → f * d < f * e :=
  arith_mul_neg_lt.corner

theorem arith_mul_neg_ge : c < 0 ∧ a ≥ b → c * a ≤ c * b := arith_mul_neg_le

theorem arith_mul_neg_ge.corner : f < 0 ∧ d ≥ e → f * d ≤ f * e :=
  arith_mul_neg_le.corner

theorem arith_mul_neg_eq : c < 0 ∧ a = b → c * a = c * b := by
  intros h
  rw [h.2]

theorem arith_mul_neg_eq.corner : f < 0 ∧ d = e → f * d = f * e := by
  intros h
  rw [h.2]

end Smt.Reconstruction.Certifying
