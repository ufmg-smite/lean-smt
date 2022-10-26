import Lean

import Smt.Reconstruction.Certifying.Pull

open Lean Elab.Tactic Meta

theorem resolution_thm : ∀ {A B C : Prop}, (A ∨ B) → (¬ A ∨ C) → B ∨ C := by
  intros A B C h₁ h₂
  cases h₁ with
  | inl ap => cases h₂ with
              | inl nap => exact (False.elim (nap ap))
              | inr cp  => exact (Or.inr cp)
  | inr bp => exact (Or.inl bp)

theorem flipped_resolution_thm : ∀ {A B C : Prop}, (¬ A ∨ B) → (A ∨ C) → B ∨ C := by
  intros A B C h₁ h₂
  cases h₁ with
  | inl nap => cases h₂ with
               | inl ap => exact False.elim (nap ap)
               | inr cp => exact (Or.inr cp)
  | inr bp => exact (Or.inl bp)

theorem resolution_thm₂ : ∀ {A C: Prop}, A → (¬ A ∨ C) → C := λ a ornac =>
  match ornac with
  | Or.inl na => False.elim (na a)
  | Or.inr c  => c

theorem flipped_resolution_thm₂ : ∀ {A C : Prop}, ¬ A → (A ∨ C) → C := λ na orac =>
  match orac with
  | Or.inl a => False.elim (na a)
  | Or.inr c => c

theorem resolution_thm₃ : ∀ {A B: Prop}, (A ∨ B) → ¬ A → B := λ orab na =>
  match orab with
  | Or.inl a => False.elim (na a)
  | Or.inr b => b

theorem flipped_resolution_thm₃ : ∀ {A B : Prop}, (¬ A ∨ B) → A → B := λ ornab a =>
  match ornab with
  | Or.inl na => False.elim (na a)
  | Or.inr b => b

theorem resolution_thm₄ : ∀ {A : Prop}, A → ¬ A → False := λ a na => na a
theorem flipped_resolution_thm₄ : ∀ {A : Prop}, ¬ A → A → False := flip resolution_thm₄

def resolutionCore (firstHyp secondHyp : Ident) (pivotTerm : Term) (flipped : Bool) : TacticM Unit := do
  let notPivot : Term := Syntax.mkApp (mkIdent `Not) #[pivotTerm]
  let mut resolvantOne  ← elabTerm pivotTerm none
  let mut resolvantTwo  ← elabTerm notPivot none
  let firstHypType  ← inferType (← elabTerm firstHyp none)
  let secondHypType ← inferType (← elabTerm secondHyp none)

  let mut len₁ :=
    match getIndex resolvantOne firstHypType with
    | none   => getLength firstHypType - (getLength resolvantOne) + 1
    | some _ => getLength firstHypType

  let mut len₂ := getLength secondHypType
  let prefixLength := len₁ - 2

  if flipped then
    let tmp      := resolvantOne
    resolvantOne := resolvantTwo
    resolvantTwo := tmp
    let tmp₂ := len₁
    len₁ := len₂
    len₂ := tmp₂

  let fident1 ← mkIdent <$> mkFreshId
  let fident2 ← mkIdent <$> mkFreshId
  pullCore resolvantOne firstHypType  firstHyp  fident1
  pullCore resolvantTwo secondHypType secondHyp fident2

  let lenGoal := len₁ + len₂ - 2
  if lenGoal > 2 then
    for s in getCongAssoc prefixLength `orAssocConv do
      evalTactic (← `(tactic| apply $s))
      logInfo m!"....apply {s}"
      printGoal

  let thmName : Name := 
    match Nat.blt 1 len₁, Nat.blt 1 len₂ with
    | true, true   => if flipped then `flipped_resolution_thm  else `resolution_thm
    | true, false  => if flipped then `flipped_resolution_thm₂ else `resolution_thm₃
    | false, true  => if flipped then `flipped_resolution_thm₃ else `resolution_thm₂
    | false, false => if flipped then `flipped_resolution_thm₄ else `resolution_thm₄

  let thm := mkIdent thmName

  logInfo m!"....closing goal with: {thm}"
  let proof := ⟨Syntax.mkApp ⟨thm⟩ #[fident1, fident2]⟩
  evalTactic (← `(tactic| exact $proof))

syntax (name := resolution_1) "R1" ident "," ident "," term : tactic
@[tactic resolution_1] def evalResolution_1 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore firstHyp secondHyp pivotTerm false

syntax (name := resolution_2) "R2" ident "," ident "," term : tactic
@[tactic resolution_2] def evalResolution_2 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore firstHyp secondHyp pivotTerm true

example : A ∨ B ∨ C ∨ D →  E ∨ F ∨ ¬ B ∨ G → E ∨ F ∨ G ∨ A ∨ C ∨ D := by
  intros h₁ h₂
  R2 h₂, h₁, B


example : ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ A → A ∨ ¬ (A ∧ B) → ¬ (A ∧ B) ∨ C ∨ ¬ D ∨ ¬ (A ∧ B) := by
  intros h₁ h₂
  R2 h₁, h₂, A

example : Eq @Eq @Eq := rfl
