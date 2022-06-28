import Smt.Reconstruction.Env
import Smt.Reconstruction.Utils
import Smt.Reconstruction.Types
import Smt.Reconstruction.Coe
import Smt.Reconstruction.Term

open Types
open proof
open term
open sort

set_option maxHeartbeats 500000

@[simp] def combineProps : Interpretation → Interpretation → (Prop → Prop → Prop) → Interpretation
| some ⟨ boolSort, k₁ ⟩, some ⟨ boolSort, k₂ ⟩, f =>
    some ⟨ boolSort, λ Γ Δ => f (k₁ Γ Δ) (k₂ Γ Δ) ⟩ -- maybe we can use state monad to avoid propagating the environments manually?
| _, _, _ => none

@[simp] def interpTerm : term → Interpretation
| term.const   n  s  => some ⟨ s, λ Γ Δ => Γ n Δ s  ⟩
| term.not     t₁    => match interpTerm t₁ with
                        | some ⟨ boolSort, k ⟩ => some ⟨ boolSort, λ Γ Δ => ¬ (k Γ Δ) ⟩
                        | _ => none
| term.and     t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ∧ p₂)
| term.or      t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ∨ p₂)
| term.implies t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ → p₂)
| term.xor     t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ≠ p₂)
| term.eq      t₁ t₂ => match interpTerm t₁, interpTerm t₂ with
                        | some ⟨ s₁, k₁ ⟩, some ⟨ s₂, k₂ ⟩ =>
                          if r: s₂ = s₁
                          then some ⟨ boolSort, λ Γ Δ =>
                                            let coercion := coe' (congrArg (interpSort Δ) r) 
                                            k₁ Γ Δ = coercion (k₂ Γ Δ) ⟩
                          else none
                        | _, _ => none
| term.bot           => some ⟨ boolSort, λ _ _ => False ⟩
| term.top           => some ⟨ boolSort, λ _ _ => True  ⟩
| term.app     t₁ t₂ => match interpTerm t₁, interpTerm t₂ with
                        | some ⟨ arrow s₁₁ s₁₂, k₁ ⟩, some ⟨ s₂, k₂ ⟩ =>
                          if r: s₂ = s₁₁
                          then some ⟨ s₁₂ , λ Γ Δ =>
                                              let coercion := coe' (congrArg (interpSort Δ) r)
                                              k₁ Γ Δ (coercion (k₂ Γ Δ)) ⟩
                          else none
                        | _, _ => none
| _ => none

@[simp] def validWith (Γ : Environment) (Δ : SEnvironment) (t : term) : Prop :=
  match interpTerm t with
  | some ⟨ boolSort, k ⟩ => Coe.coe (k Γ Δ)
  | _ => False

def followsFrom (t₁ t₂ : term) : Prop :=
  ∀ {Γ : Environment} {Δ : SEnvironment}, validWith Γ Δ t₁ → validWith Γ Δ t₂

@[simp] def wellTyped (t : term) : Prop := isSome (interpTerm t)

@[simp] def getInterp (t : term) (h : wellTyped t) : Σ (s : sort), Environment → (Δ : SEnvironment) → interpSort Δ s :=
  match r: interpTerm t with
  | some ⟨ s, k ⟩ => ⟨ s, k ⟩
  | none => by simp at h; rewrite [r] at h; exact (False.elim h)

