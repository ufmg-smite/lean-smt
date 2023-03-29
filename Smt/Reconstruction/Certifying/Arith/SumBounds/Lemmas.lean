/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Monoid.Lemmas -- add_lt_add
import Mathlib.Init.Function -- swap

open Function

namespace Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas

variable {α : Type}

variable [Preorder α]
variable [Add α]
variable [CovariantClass α α (· + ·) (· < ·)]
variable [CovariantClass α α (· + ·) (· ≤ ·)]
variable [CovariantClass α α (swap (· + ·)) (· < ·)]
variable [CovariantClass α α (swap (· + ·)) (· ≤ ·)]

variable {a b c d : α}

theorem sumBounds₁ : a < b → c < d → a + c < b + d := by
    intros h₁ h₂
    have r₁: a + c < a + d := add_lt_add_left h₂ a
    have r₂: a + d < b + d := add_lt_add_right h₁ d
    exact lt_trans r₁ r₂

theorem sumBounds₂ : a < b → c ≤ d → a + c < b + d := by
  intros h₁ h₂
  have r₁: a + c ≤ a + d := add_le_add_left h₂ a
  have r₂: a + d < b + d := add_lt_add_right h₁ d
  exact lt_of_le_of_lt r₁ r₂

theorem sumBounds₃ : a < b → c = d → a + c < b + d := by
  intros h₁ h₂
  rewrite [h₂]
  exact add_lt_add_right h₁ d

theorem sumBounds₄ : a ≤ b → c < d → a + c < b + d := by
  intros h₁ h₂
  have r₁ : a + c < a + d := add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := add_le_add_right h₁ d
  exact lt_of_lt_of_le r₁ r₂

theorem sumBounds₅ : a ≤ b → c ≤ d → a + c ≤ b + d := by
  intros h₁ h₂
  have r₁ : a + c ≤ a + d := add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := add_le_add_right h₁ d
  exact le_trans r₁ r₂

theorem sumBounds₆ : a ≤ b → c = d → a + c ≤ b + d := by
  intros h₁ h₂
  rewrite [h₂]
  exact add_le_add_right h₁ d

theorem sumBounds₇ : a = b → c < d → a + c < b + d := by
  intros h₁ h₂
  rewrite [h₁]
  exact add_lt_add_left h₂ b

theorem sumBounds₈ : a = b → c ≤ d → a + c ≤ b + d := by
  intros h₁ h₂
  rewrite [h₁]
  exact add_le_add_left h₂ b

theorem sumBounds₉ : a = b → c = d → a + c ≤ b + d := by
  intros h₁ h₂
  rewrite [h₁, h₂]
  exact le_refl (b + d)

end Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas
