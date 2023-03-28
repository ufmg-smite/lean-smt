import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.PermutateOr

import Mathlib.Init.Algebra.Order

open Smt.Reconstruction.Certifying

variable {α : Type}

variable [LinearOrder α]

variable {a b : α}

theorem trichotomy₁ : ¬ a < b → ¬ a = b → a > b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  exact (orImplies₃ ((orImplies₃ tr) h₁)) h₂

theorem trichotomy₂ : ¬ a = b → ¬ a < b → a > b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  exact (orImplies₃ ((orImplies₃ tr) h₂)) h₁

theorem trichotomy₃ : ¬ a < b → ¬ a > b → a = b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  have tr' := by permutateOr tr, [0, 2, 1]
  exact (orImplies₃ ((orImplies₃ tr') h₁)) h₂
  
theorem trichotomy₄ : ¬ a > b → ¬ a < b → a = b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  have tr' := by permutateOr tr, [0, 2, 1]
  exact (orImplies₃ ((orImplies₃ tr') h₂)) h₁

theorem trichotomy₅ : ¬ a = b → ¬ a > b → a < b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  have tr' := by permutateOr tr, [1, 2, 0]
  exact (orImplies₃ ((orImplies₃ tr') h₁)) h₂

theorem trichotomy₆ : ¬ a > b → ¬ a = b → a < b := by
  intros h₁ h₂
  have tr := lt_trichotomy a b
  have tr' := by permutateOr tr, [1, 2, 0]
  exact (orImplies₃ ((orImplies₃ tr') h₂)) h₁

theorem not_gt_of_le : a ≤ b → ¬ a > b :=
  λ h₁ h₂ => absurd h₂ (not_lt_of_ge h₁)
#check @not_gt_of_le
