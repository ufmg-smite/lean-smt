import Smt.Reconstruction.Defs
import Smt.Reconstruction.Term

open Types
open proof
open term
open sort
open Nat

namespace Rules

theorem refl : ∀ {t : term} {Γ : Environment} {Δ : SEnvironment},
  validWith Γ Δ (eq t t)
  | t, Γ, Δ =>
    match r: interpTerm t with
    | ⟨ atom 0 , _ ⟩               => by simp; rewrite [r]; exact rfl
    | ⟨ atom 1 , _ ⟩               => by simp; rewrite [r]; exact rfl
    | ⟨ atom (succ (succ _)) , _ ⟩ => by simp; rewrite [r]; simp; exact rfl
    | ⟨ sort.undef, _ ⟩            => by simp; rewrite [r]; exact rfl
    | ⟨ sort.array _ _, _ ⟩        => by simp; rewrite [r]; simp; exact rfl
    | ⟨ sort.bv _, _ ⟩             => by simp; rewrite [r]; simp; exact rfl
    | ⟨ sort.arrow _ _, _ ⟩        => by simp; rewrite [r]; simp; exact rfl
    | ⟨ sort.dep, _ ⟩              => by simp; rewrite [r]; exact rfl

/- theorem symm : ∀ {t₁ t₂ : term}, followsFrom (eq t₁ t₂) (eq t₂ t₁) -/
/-   | t₁, t₂, Γ, Δ, h => -/
/-     by simp at * -/
/-        split at h -/
/-        case h_1 a k h' => -/
/-          split at h' -/
/-          case h_1 c k₁ k₂ rt₁ rt₂ => -/
/-            have smth := by injection h' with h'; injection h' with _ h'; exact h' -/
/-            rewrite [← smth] at h -/
/-            exact (Eq.symm h) -/
/-          case h_2 => simp at h' -/
/-        case h_2 => simp at h -/


end Rules
