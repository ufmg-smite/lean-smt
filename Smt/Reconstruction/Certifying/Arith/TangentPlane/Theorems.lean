/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Tactic.Linarith

variable (α : Type)

variable [LinearOrderedField α]

variable (x y a b : α)

-- SIGMA = -1

theorem arithMulTangentMpLower :
    x * y ≤ b * x + a * y - a * b →
    ((x ≤ a ∧ y ≥ b) ∨ (x ≥ a ∧ y ≤ b)) :=
  by intro h
     have h₁ : (x - a) * (y - b) ≤ 0 := by linarith
     exact
       match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
       | Or.inl xaNeg,           Or.inl ybNeg           => by nlinarith
       | Or.inl xaNeg,           Or.inr (Or.inl ybZero) => by
         have xaNeg' := le_of_lt xaNeg
         simp at xaNeg'
         have ybZero' := ge_of_eq ybZero
         simp at ybZero'
         exact Or.inl (And.intro xaNeg' ybZero')
       | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  => by
         have xaNeg' := le_of_lt xaNeg
         simp at xaNeg'
         have ybPos' := le_of_lt ybPos
         simp at ybPos'
         exact Or.inl (And.intro xaNeg' ybPos')
       | Or.inr (Or.inl xaZero), Or.inl ybNeg           => by
         have xaZero' := ge_of_eq xaZero 
         simp at xaZero'
         have ybNeg' := le_of_lt ybNeg
         simp at ybNeg'
         exact Or.inr (And.intro xaZero' ybNeg')
       | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) => by
         have xaZero' := le_of_eq xaZero
         simp at xaZero'
         have ybZero' := ge_of_eq ybZero
         simp at ybZero'
         exact Or.inl (And.intro xaZero' ybZero')
       | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  => by
         have xaZero' := le_of_eq xaZero
         simp at xaZero'
         have ybPos' := le_of_lt ybPos
         simp at ybPos'
         exact Or.inl (And.intro xaZero' ybPos')
       | Or.inr (Or.inr xaPos),  Or.inl ybNeg           => by
         have xaPos' := le_of_lt xaPos
         simp at xaPos'
         have ybNeg' := le_of_lt ybNeg
         simp at ybNeg'
         exact Or.inr (And.intro xaPos' ybNeg')
       | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) => by
         have xaPos' := le_of_lt xaPos
         simp at xaPos'
         have ybZero' := le_of_eq ybZero
         simp at ybZero'
         exact Or.inr (And.intro xaPos' ybZero')
       | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  => by nlinarith

theorem arithMulTangentMprLower :
    ((x ≤ a ∧ y ≥ b) ∨ (x ≥ a ∧ y ≤ b)) →
    x * y ≤ b * x + a * y - a * b := fun h =>
  match h with
  | Or.inl (And.intro h₁ h₂) => by nlinarith
  | Or.inr (And.intro h₁ h₂) => by nlinarith
    /- have h₁' : (x - a ≥ 0) := by linarith -/
    /- have h₂' : (y - b ≤ 0) := by linarith -/
    /- have prod_nonpos := mul_nonpos_of_nonneg_of_nonpos h₁' h₂' -/
    /- linarith -/

theorem arithMulTangentLower :
    x * y ≤ b * x + a * y - a * b ↔ 
    ((x ≤ a ∧ y ≥ b) ∨ (x ≥ a ∧ y ≤ b)) :=
  ⟨ arithMulTangentMpLower α x y a b , arithMulTangentMprLower α x y a b  ⟩

-- SIGMA = 1
     
theorem arithMulTangentMpUpper :
    x * y ≥ b * x + a * y - a * b →
    ((x ≤ a ∧ y ≤ b) ∨ (x ≥ a ∧ y ≥ b)) :=
  by intro h
     have h₁ : (x - a) * (y - b) ≥ 0 := by linarith
     exact
       match lt_trichotomy (x - a) 0, lt_trichotomy (y - b) 0 with
       | Or.inl xaNeg,           Or.inl ybNeg           => by
         have xaNeg' := le_of_lt xaNeg
         simp at xaNeg'
         have ybNeg' := le_of_lt ybNeg
         simp at ybNeg'
         exact Or.inl (And.intro xaNeg' ybNeg')
       | Or.inl xaNeg,           Or.inr (Or.inl ybZero) => by
         have xaNeg' := le_of_lt xaNeg
         simp at xaNeg'
         have ybZero' := le_of_eq ybZero
         simp at ybZero'
         exact Or.inl (And.intro xaNeg' ybZero')
       | Or.inl xaNeg,           Or.inr (Or.inr ybPos)  => by nlinarith
       | Or.inr (Or.inl xaZero), Or.inl ybNeg           => by
         have xaZero' := le_of_eq xaZero 
         simp at xaZero'
         have ybNeg' := le_of_lt ybNeg
         simp at ybNeg'
         exact Or.inl (And.intro xaZero' ybNeg')
       | Or.inr (Or.inl xaZero), Or.inr (Or.inl ybZero) => by
         have xaZero' := le_of_eq xaZero
         simp at xaZero'
         have ybZero' := le_of_eq ybZero
         simp at ybZero'
         exact Or.inl (And.intro xaZero' ybZero')
       | Or.inr (Or.inl xaZero), Or.inr (Or.inr ybPos)  => by
         have xaZero' := ge_of_eq xaZero
         simp at xaZero'
         have ybPos' := le_of_lt ybPos
         simp at ybPos'
         exact Or.inr (And.intro xaZero' ybPos')
       | Or.inr (Or.inr xaPos),  Or.inl ybNeg           => by nlinarith
       | Or.inr (Or.inr xaPos),  Or.inr (Or.inl ybZero) => by
         have xaPos' := le_of_lt xaPos
         simp at xaPos'
         have ybZero' := ge_of_eq ybZero
         simp at ybZero'
         exact Or.inr (And.intro xaPos' ybZero')
       | Or.inr (Or.inr xaPos),  Or.inr (Or.inr ybPos)  => by
         have xaPos' := le_of_lt xaPos
         simp at xaPos'
         have ybPos' := le_of_lt ybPos
         simp at ybPos'
         exact Or.inr (And.intro xaPos' ybPos')

theorem arithMulTangentMprUpper :
    ((x ≤ a ∧ y ≤ b) ∨ (x ≥ a ∧ y ≥ b)) →
    x * y ≥ b * x + a * y - a * b := fun h =>
  match h with
  | Or.inl (And.intro h₁ h₂) => by nlinarith
  | Or.inr (And.intro h₁ h₂) => by nlinarith

theorem arithMulTangentUpper :
    x * y ≥ b * x + a * y - a * b ↔ 
    ((x ≤ a ∧ y ≤ b) ∨ (x ≥ a ∧ y ≥ b)) :=
  ⟨ arithMulTangentMpUpper α x y a b , arithMulTangentMprUpper α x y a b  ⟩

