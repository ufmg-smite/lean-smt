import Smt.Reconstruction.Env
import Smt.Reconstruction.Types
import Smt.Reconstruction.Coe
import Smt.Reconstruction.Term

open Types
open proof
open term
open sort

set_option maxHeartbeats 500000

def typeErr : Interpretation := ⟨ boolSort, λ _ _ => True ⟩

@[simp] def combineProps : Interpretation → Interpretation → (Prop → Prop → Prop) → Interpretation
| ⟨ boolSort, k₁ ⟩, ⟨ boolSort, k₂ ⟩, f =>
    ⟨ boolSort, λ Γ Δ => f (k₁ Γ Δ) (k₂ Γ Δ) ⟩ -- maybe we can use state monad to avoid propagating the environments manually?
| _, _, _ => typeErr

@[simp] def interpTerm : term → Interpretation
| term.const   n  s  => ⟨ s, λ Γ Δ => Γ n Δ s ⟩
| term.not     t₁    => match interpTerm t₁ with
                        | ⟨ boolSort, k ⟩ => ⟨ boolSort, λ Γ Δ => ¬ (k Γ Δ) ⟩
                        | _ => typeErr
| term.and     t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ∧ p₂)
| term.or      t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ∨ p₂)
| term.implies t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ → p₂)
| term.xor     t₁ t₂ => combineProps (interpTerm t₁) (interpTerm t₂) (λ p₁ p₂ => p₁ ≠ p₂)
| term.eq      t₁ t₂ => match interpTerm t₁, interpTerm t₂ with
                        | ⟨ s₁, k₁ ⟩, ⟨ s₂, k₂ ⟩ =>
                          if r: s₂ = s₁
                          then ⟨ boolSort, λ Γ Δ =>
                                            let coercion := coe' (congrArg (interpSort Δ) r) 
                                            k₁ Γ Δ = coercion (k₂ Γ Δ) ⟩
                          else typeErr
| term.bot           => ⟨ boolSort, λ _ _ => False ⟩
| term.top           => ⟨ boolSort, λ _ _ => True  ⟩
| term.app     t₁ t₂ => match interpTerm t₁, interpTerm t₂ with
                        | ⟨ arrow s₁₁ s₁₂, k₁ ⟩, ⟨ s₂, k₂ ⟩ =>
                          if r: s₂ = s₁₁
                          then ⟨ s₁₂ , λ Γ Δ =>
                                         let coercion := coe' (congrArg (interpSort Δ) r)
                                         k₁ Γ Δ (coercion (k₂ Γ Δ)) ⟩
                          else typeErr
                        | _, _ => typeErr
| _ => typeErr

@[simp] def validWith (Γ : Environment) (Δ : SEnvironment) (t : term) : Prop :=
  match interpTerm t with
  | ⟨ boolSort, k ⟩ => Coe.coe (k Γ Δ)
  | _ => False

def followsFrom (t₁ t₂ : term) : Prop :=
  ∀ {Γ : Environment} {Δ : SEnvironment}, validWith Γ Δ t₁ → validWith Γ Δ t₂

/- @[simp] def wellTyped (t : term) : Prop := isSome (interpTerm t) -/

/- @[simp] def getInterp (t : term) (h : wellTyped t) : Σ (s : sort), Environment → (Δ : SEnvironment) → interpSort Δ s := -/
/-   match r: interpTerm t with -/
/-   | some ⟨ s, k ⟩ => ⟨ s, k ⟩ -/
/-   | none => by simp at h; rewrite [r] at h; exact (False.elim h) -/

