import Smt

open Smt.Reconstruction.Certifying

example : A ∨ B ∨ C ∨ D → E ∨ ¬ C ∨ F ∨ G → A ∨ B ∨ D ∨ E ∨ F ∨ G := by
  intros h₁ h₂
  R1 h₁, h₂, C, [-1, -1]

example : A ∨ B ∨ C ∨ D → E ∨ ¬ B → A ∨ (C ∨ D) ∨ E := by
  intros h₁ h₂
  R1 h₁, h₂, B, [2, 1]

example : ¬ A → B ∨ A ∨ C → B ∨ C := by
  intros h₁ h₂
  R2 h₁, h₂, A, [0, 2]

example : ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ A → A ∨ ¬ (A ∧ B) → ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ (A ∧ B) := by
  intros h₁ h₂
  R2 h₁, h₂, A

example : A ∨ B ∨ C ∨ D → ¬ A → B ∨ C ∨ D := by
  intros h₁ h₂
  R1 h₁, h₂, A

example : B ∨ A ∨ C ∨ A → D ∨ ¬ A ∨ E ∨ ¬ A ∨ F → B ∨ C ∨ A ∨ D ∨ E ∨ ¬ A ∨ F  := by
  intros h₁ h₂
  R1 h₁, h₂, A

example : A → ¬ A → False := by
  intros h₁ h₂
  R1 h₁, h₂, A

