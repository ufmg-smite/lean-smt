import Smt.Reconstruction.Defs
import Smt.Reconstruction.Term

open Types
open proof
open term
open sort
open Nat

namespace Rules

syntax "absurdHyp" ident "(" ident,+ ")" : tactic
macro_rules
  | `(tactic| absurdHyp $h:ident ($n:ident)) => `(tactic| rewrite [($n)] at ($h); have z: False := ($h); cases z)
  | `(tactic| absurdHyp $h:ident ($n:ident, $m:ident)) => `(tactic| rewrite [($n), ($m)] at ($h); have z: False := ($h); simp at z)

open Classical

theorem notImplies1 : ∀ {t₁ t₂ : term},
  followsFrom (not $ implies t₁ t₂) t₁ :=
  by intros t₁ t₂ Γ Δ h
     simp at h
     split at h
     case h_1 _ k h' =>
       split at h'
       case h_1 _ k' h'' =>
         split at h''
         case h_1 _ k₁ k₂ rt₁ rt₂ =>
           simp
           rewrite [rt₁]
           have ek : (fun Γ Δ => ¬ k' Γ Δ) = k :=
             by injection h' with h'; injection h' with _ h'; exact h';
           have fe : (fun Γ Δ => k₁ Γ Δ → k₂ Γ Δ) = k' :=
             by injection h'' with h''; injection h'' with _ h''; exact h''
           rewrite [← ek, ← fe] at h
           apply byContradiction
           exact (λ hf => h (λ k₁w => False.elim (hf k₁w)))
         case h_2 => simp at h''
       case h_2 => simp at h'
     case h_2 => exact (False.elim h)

theorem notImplies2 : ∀ {t₁ t₂ : term},
  followsFrom (not $ implies t₁ t₂) (not t₂) :=
    by intros t₁ t₂ Γ Δ h
       simp at h
       match r₁: interpTerm t₁, r₂: interpTerm t₂ with
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 1, k₂ ⟩ =>
           simp
           rewrite [r₂]
           show ¬ k₂ Γ Δ
           rewrite [r₁, r₂] at h
           have h₂ : ¬ ((k₁ Γ Δ) → (k₂ Γ Δ)) := h
           match em (k₂ Γ Δ) with
           | Or.inl r  => exact False.elim (h₂ (λ _ => r))
           | Or.inr r  => exact r
       | some ⟨ atom 0, _ ⟩, _  => rewrite [r₁] at h; simp at h
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 0, _ ⟩  => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom (succ (succ _)), _ ⟩ => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.undef, _ ⟩           => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.array _ _, _ ⟩       => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.bv _, _ ⟩            => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.arrow _ _, _ ⟩       => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.dep, _ ⟩             => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, none                             => absurdHyp h (r₁, r₂)
       | some ⟨ atom (succ (succ _)), _ ⟩, _ => absurdHyp h (r₁) 
       | some ⟨ sort.undef, _ ⟩, _           => absurdHyp h (r₁) 
       | some ⟨ sort.array _ _, _ ⟩, _       => absurdHyp h (r₁) 
       | some ⟨ sort.bv _, _ ⟩, _            => absurdHyp h (r₁) 
       | some ⟨ sort.arrow _ _, _ ⟩, _       => absurdHyp h (r₁) 
       | some ⟨ sort.dep, _ ⟩, _             => absurdHyp h (r₁)
       | none, _                             => absurdHyp h (r₁)

theorem impliesElim : ∀ {t₁ t₂ : term},
  followsFrom (implies t₁ t₂) (or (not t₁) t₂)
  | t₁, t₂, Γ, Δ, h =>
    by simp at h
       match r₁: interpTerm t₁, r₂: interpTerm t₂ with
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 1, k₂ ⟩ =>
           simp
           rewrite [r₁, r₂]
           rewrite [r₁, r₂] at h
           show (¬ k₁ Γ Δ) ∨ (k₂ Γ Δ)
           have h₂ : k₁ Γ Δ → k₂ Γ Δ := h
           match em (k₁ Γ Δ), em (k₂ Γ Δ) with
           | Or.inl _, Or.inl k₂W => exact Or.inr k₂W
           | Or.inl k₁W, Or.inr nk₂W => have k₂W := h₂ k₁W
                                        exact (False.elim (nk₂W k₂W))
           | Or.inr _, Or.inl k₂W => exact Or.inr k₂W
           | Or.inr nk₁W, Or.inr _ => exact Or.inl nk₁W
       | some ⟨ atom 0, _ ⟩, _  => absurdHyp h (r₁)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 0, _ ⟩  => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ atom (succ (succ _)), _ ⟩ => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.undef, _ ⟩           => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.array _ _, _ ⟩       => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.bv _, _ ⟩            => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.arrow _ _, _ ⟩       => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, some ⟨ sort.dep, _ ⟩             => absurdHyp h (r₁, r₂)
       | some ⟨ atom 1, k₁ ⟩, none                             => absurdHyp h (r₁, r₂)
       | some ⟨ atom (succ (succ _)), _ ⟩, _ => absurdHyp h (r₁) 
       | some ⟨ sort.undef, _ ⟩, _           => absurdHyp h (r₁) 
       | some ⟨ sort.array _ _, _ ⟩, _       => absurdHyp h (r₁)
       | some ⟨ sort.bv _, _ ⟩, _            => absurdHyp h (r₁)
       | some ⟨ sort.arrow _ _, _ ⟩, _       => absurdHyp h (r₁)
       | some ⟨ sort.dep, _ ⟩, _             => absurdHyp h (r₁)
       | none, _                             => absurdHyp h (r₁)

theorem contradiction: ∀ {t: term},
  followsFrom (and (not t) t) bot
  | t, Γ, Δ, h => by
    simp at h
    match r: interpTerm t with
    | some ⟨ atom 1, k ⟩ =>
        rewrite [r] at h;
        simp at h
        have ⟨nkW, kW⟩ : ¬ (k Γ Δ) ∧ k Γ Δ := h
        exact False.elim (nkW kW)
    | some ⟨ atom 0, _ ⟩               => absurdHyp h (r)
    | some ⟨ atom (succ (succ _)), _ ⟩ => absurdHyp h (r)
    | some ⟨ sort.undef, _ ⟩           => absurdHyp h (r)
    | some ⟨ sort.array _ _, _ ⟩       => absurdHyp h (r)
    | some ⟨ sort.bv _, _ ⟩            => absurdHyp h (r)
    | some ⟨ sort.arrow _ _, _ ⟩       => absurdHyp h (r)
    | some ⟨ sort.dep, _ ⟩             => absurdHyp h (r)
    | none                             => absurdHyp h (r)
       
theorem R1 : ∀ {t₁ t₂ : term},
  followsFrom (and (or (not t₁) t₂) t₁) t₂
  | t₁, t₂, Γ, Δ, h => by
    simp at h
    match r₁: interpTerm t₁, r₂: interpTerm t₂ with
    | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 1, k₂ ⟩ =>
        simp at *
        rewrite [r₁, r₂] at h
        rewrite [r₂]
        have ⟨ H, k₁W ⟩: ((¬ (k₁ Γ Δ)) ∨ (k₂ Γ Δ)) ∧ (k₁ Γ Δ) := h
        match em (k₂ Γ Δ) with
        | Or.inl k₂W  => exact k₂W
        | Or.inr _    => match em (k₁ Γ Δ) with
                         | Or.inl k₁W  => match H with
                                          | Or.inl nk₁W => exact (False.elim (nk₁W k₁W))
                                          | Or.inr k₂W  => exact k₂W
                         | Or.inr nk₁W => exact (False.elim (nk₁W k₁W))
    | some ⟨ atom 1, _ ⟩, some ⟨ atom 0, _ ⟩               => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ atom (succ (succ _)), _ ⟩ => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.undef, _ ⟩           => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.array _ _, _ ⟩       => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.bv _, _ ⟩            => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.arrow _ _, _ ⟩       => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.dep, _ ⟩             => absurdHyp h (r₁, r₂)
    | some ⟨ atom 1, _ ⟩, none                             => absurdHyp h (r₁, r₂)
    | some ⟨ atom 0, _ ⟩, _               => absurdHyp h (r₁) 
    | some ⟨ atom (succ (succ _)), _ ⟩, _ => absurdHyp h (r₁)
    | some ⟨ sort.undef, _ ⟩, _           => absurdHyp h (r₁)
    | some ⟨ sort.array _ _, _ ⟩, _       => absurdHyp h (r₁)
    | some ⟨ sort.bv _, _ ⟩, _            => absurdHyp h (r₁)
    | some ⟨ sort.arrow _ _, _ ⟩, _       => absurdHyp h (r₁)
    | some ⟨ sort.dep, _ ⟩, _             => absurdHyp h (r₁)
    | none, _                             => absurdHyp h (r₁)

theorem conjunction: ∀ {t₁ t₂: term} {Γ: Environment} {Δ : SEnvironment},
  validWith Γ Δ t₁ → validWith Γ Δ t₂ → validWith Γ Δ (and t₁ t₂)
  | t₁, t₂, Γ, Δ, h₁, h₂ => by
    simp at *
    match r₁: interpTerm t₁, r₂: interpTerm t₂ with
    | some ⟨ atom 1, k₁ ⟩, some ⟨ atom 1, k₂ ⟩ =>
        show (k₁ Γ Δ) ∧ (k₂ Γ Δ)
        simp
        rewrite [r₁] at h₁
        rewrite [r₂] at h₂
        have k₁W: (k₁ Γ Δ) := h₁
        have k₂W: (k₂ Γ Δ) := h₂
        exact And.intro k₁W k₂W
    | some ⟨ atom 1, _ ⟩, some ⟨ atom 0, _ ⟩               => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ atom (succ (succ _)), _ ⟩ => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.undef, _ ⟩           => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.array _ _, _ ⟩       => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.bv _, _ ⟩            => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.arrow _ _, _ ⟩       => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, some ⟨ sort.dep, _ ⟩             => absurdHyp h₂ (r₂)
    | some ⟨ atom 1, _ ⟩, none                             => absurdHyp h₂ (r₂)
    | some ⟨ atom 0, _ ⟩, _                                => absurdHyp h₁ (r₁)
    | some ⟨ atom (succ (succ _)), _ ⟩ , _ => absurdHyp h₁ (r₁)
    | some ⟨ sort.undef, _ ⟩, _            => absurdHyp h₁ (r₁)
    | some ⟨ sort.array _ _, _ ⟩, _        => absurdHyp h₁ (r₁)
    | some ⟨ sort.bv _, _ ⟩, _             => absurdHyp h₁ (r₁)
    | some ⟨ sort.arrow _ _, _ ⟩, _        => absurdHyp h₁ (r₁)
    | some ⟨ sort.dep, _ ⟩, _              => absurdHyp h₁ (r₁)
    | none, _                              => absurdHyp h₁ (r₁)

theorem followsBot: ∀ {t: term},
  followsFrom t bot → ∀ {Γ : Environment} {Δ : SEnvironment}, ¬ validWith Γ Δ t
  | t, h, Γ, Δ => by
    intro validT
    have validBot := @h Γ Δ validT
    simp at validBot
    cases validBot

@[simp] def isBool : term → Bool
  | t => match interpTerm t with
         | some ⟨ atom 1, _ ⟩ => true
         | _ => false

theorem interpNotTerm: ∀ {Γ: Environment} {Δ: SEnvironment} {t: term},
  isBool t → ¬ validWith Γ Δ (not t) → validWith Γ Δ t
  | Γ, Δ, t, bt, h => by
    simp
    match r: interpTerm t with
    | some ⟨ atom 1, k ⟩ => match em (k Γ Δ) with
                            | Or.inl kW  => exact kW
                            | Or.inr nkW => simp at h
                                            rewrite [r] at h
                                            have nnkW : ¬ (¬ (k Γ Δ)) := h
                                            exact (False.elim (nnkW nkW))
    | some ⟨ atom 0, _ ⟩               => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ atom (succ (succ _)), _ ⟩ => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ sort.undef, _ ⟩           => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ sort.array _ _, _ ⟩       => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ sort.bv _, _ ⟩            => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ sort.arrow _ _, _ ⟩       => simp at bt; rewrite [r] at bt; cases bt
    | some ⟨ sort.dep, _ ⟩             => simp at bt; rewrite [r] at bt; cases bt
    | none                             => simp at bt; rewrite [r] at bt; cases bt

end Rules
