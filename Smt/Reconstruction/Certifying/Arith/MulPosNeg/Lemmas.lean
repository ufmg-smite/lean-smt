/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

namespace Smt.Reconstruction.Certifying

variable {α : Type}

variable [LinearOrderedRing α]

variable {a b c : α}

theorem arith_mul_pos_lt : a < b → c > 0 → c * a < c * b := mul_lt_mul_of_pos_left
theorem arith_mul_pos_le : a ≤ b → c > 0 → c * a ≤ c * b := λ h₁ h₂ =>
  mul_le_mul_of_nonneg_left h₁ (le_of_lt h₂)
theorem arith_mul_pos_gt : a > b → c > 0 → c * a > c * b := arith_mul_pos_lt
theorem arith_mul_pos_ge : a ≥ b → c > 0 → c * a ≥ c * b := arith_mul_pos_le

theorem arith_mul_neg_lt : a < b → c < 0 → c * a > c * b := mul_lt_mul_of_neg_left
theorem arith_mul_neg_le : a ≤ b → c < 0 → c * a ≥ c * b := λ h₁ h₂ =>
  (mul_le_mul_left_of_neg h₂).mpr h₁
theorem arith_mul_neg_gt : a > b → c < 0 → c * a < c * b := arith_mul_neg_lt
theorem arith_mul_neg_ge : a ≥ b → c < 0 → c * a ≤ c * b := arith_mul_neg_le

end Smt.Reconstruction.Certifying
