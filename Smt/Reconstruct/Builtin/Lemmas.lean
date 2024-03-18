/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Builtin

theorem iteElim1 [hc : Decidable c] : ite c a b → ¬ c ∨ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem iteElim2 [hc : Decidable c] : ite c a b → c ∨ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem notIteElim1 [hc : Decidable c] : ¬ ite c a b → ¬ c ∨ ¬ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem notIteElim2 [hc : Decidable c] : ¬ ite c a b → c ∨ ¬ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem cnfItePos1 [h : Decidable c] : ¬ (ite c a b) ∨ ¬ c ∨ a := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isTrue _    => exact Or.inr hite'
  | isFalse hnc => exact Or.inl hnc

theorem cnfItePos2 [h : Decidable c] : ¬ (ite c a b) ∨ c ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue hc => exact Or.inl hc

theorem cnfItePos3 [h : Decidable c] : ¬ (ite c a b) ∨ a ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue _  => exact Or.inl hite'

theorem cnfIteNeg1 [h : Decidable c] : (ite c a b) ∨ ¬ c ∨ ¬ a := by
  apply orImplies
  intro hnite
  match h with
  | isTrue _    => exact Or.inr hnite
  | isFalse hnc => exact Or.inl hnc

theorem cnfIteNeg2 [h : Decidable c] : (ite c a b) ∨ c ∨ ¬ b   := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue hc => exact Or.inl hc

theorem cnfIteNeg3 [h : Decidable c] : (ite c a b) ∨ ¬ a ∨ ¬ b := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue _  => exact Or.inl hnite

theorem scopes : ∀ {ps : List Prop} {q : Prop}, impliesN ps q → andN ps → q :=
  by intros ps q h
     match ps with
     | []   => intro; exact h
     | [p]  => unfold andN
               unfold impliesN at h
               exact h
     | p₁::p₂::ps => unfold andN
                     unfold impliesN at h
                     intro ⟨hp₁, hps⟩
                     revert hps
                     exact scopes (h hp₁)

end Smt.Reconstruct.Builtin
