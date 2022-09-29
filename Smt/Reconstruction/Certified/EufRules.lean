import Smt.Reconstruction.Defs
import Smt.Reconstruction.Term

open Types
open proof
open term
open sort
open Nat

namespace Rules

theorem refl : ∀ {t : term} {Γ : Environment} {Δ : SEnvironment},
  wellTyped t → validWith Γ Δ (eq t t)
  | t, Γ, Δ, wTt =>
    match r: interpTerm t with
    | some ⟨ atom 0 , _ ⟩               => by simp; rewrite [r]; exact rfl
    | some ⟨ atom 1 , _ ⟩               => by simp; rewrite [r]; exact rfl
    | some ⟨ atom (succ (succ _)) , _ ⟩ => by simp; rewrite [r]; simp; exact rfl
    | some ⟨ sort.undef, _ ⟩            => by simp; rewrite [r]; exact rfl
    | some ⟨ sort.array _ _, _ ⟩        => by simp; rewrite [r]; simp; exact rfl
    | some ⟨ sort.bv _, _ ⟩             => by simp; rewrite [r]; simp; exact rfl
    | some ⟨ sort.arrow _ _, _ ⟩        => by simp; rewrite [r]; simp; exact rfl
    | some ⟨ sort.dep, _ ⟩              => by simp; rewrite [r]; exact rfl
    | none                              => by simp at wTt; rewrite [r] at wTt; exact False.elim wTt


end Rules
