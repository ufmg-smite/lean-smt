import Smt

open Smt.Reconstruction.Certifying

example : A ∨ B ∨ C ∨ D → E ∨ ¬ C ∨ F ∨ G → A ∨ B ∨ D ∨ E ∨ F ∨ G := by
  intros h₁ h₂
  R1 h₁, h₂, C, [-1, -1]

example : A ∨ B ∨ C ∨ D → E ∨ F ∨ ¬ B ∨ H → A ∨ (C ∨ D) ∨ E ∨ F ∨ H := by
  intros h₁ h₂
  R1 h₁, h₂, B, [2, -1]

example : ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ A → A ∨ ¬ (A ∧ B) → ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ (A ∧ B) := by
  intros h₁ h₂
  R2 h₁, h₂, A

example : A ∨ B ∨ C ∨ D → ¬ A → B ∨ C ∨ D := by
  intros h₁ h₂
  R1 h₁, h₂, A
