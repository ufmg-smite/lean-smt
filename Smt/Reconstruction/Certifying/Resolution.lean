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

theorem resolution_thm₂ : ∀ {A C: Prop}, A → (¬ A ∨ C) → C := λ a ornac =>
  match ornac with
  | Or.inl na => False.elim (na a)
  | Or.inr c  => c

theorem resolution_thm₃ : ∀ {A B: Prop}, (A ∨ B) → ¬ A → B := λ orab na =>
  match orab with
  | Or.inl a => False.elim (na a)
  | Or.inr b => b

theorem resolution_thm₄ : ∀ {A : Prop}, A → ¬ A → False := λ a na => na a

def resolutionCore (firstHyp secondHyp : Ident) (pivotTerm : Term) : TacticM Unit := do
  let fident1 ← mkIdent <$> mkFreshId
  let fident2 ← mkIdent <$> mkFreshId
  let notPivot : Term := Syntax.mkApp (mkIdent `Not) #[pivotTerm]
  let pivotExpr     ← elabTerm pivotTerm none
  let notPivotExpr  ← elabTerm notPivot none
  let firstHypType  ← inferType (← elabTerm firstHyp none)
  let secondHypType ← inferType (← elabTerm secondHyp none)

  let lenGoal ← getLength <$> getMainTarget
  pullCore pivotExpr    firstHypType  firstHyp  fident1
  pullCore notPivotExpr secondHypType secondHyp fident2

  let mut len₁ := getLength firstHypType
  if Option.isNone (getIndex pivotExpr firstHypType) then
    len₁ := len₁ - (getLength pivotExpr) + 1

  let len₂ := getLength secondHypType

  if lenGoal > 2 then
    for s in getCongAssoc (len₁ - 2) `orAssocConv do
      evalTactic (← `(tactic| apply $s))
      logInfo m!"....apply {s}"
      printGoal

  if len₁ > 1 then
    if len₂ > 1 then
      evalTactic (← `(tactic| exact resolution_thm $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm"
    else
      evalTactic (← `(tactic| exact resolution_thm₃ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₃"
  else
    if len₂ > 1 then
      evalTactic (← `(tactic| exact resolution_thm₂ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₂"
    else
      evalTactic (← `(tactic| exact resolution_thm₄ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₄"

syntax (name := resolution_1) "R1" ident "," ident "," term : tactic
@[tactic resolution_1] def evalResolution_1 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore firstHyp secondHyp pivotTerm

syntax (name := resolution_2) "R2" ident "," ident "," term : tactic
@[tactic resolution_2] def evalResolution_2 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore secondHyp firstHyp pivotTerm

example : A ∨ B ∨ D ∨ (W ∨ Z) → E ∨ F ∨ G ∨ ¬ (W ∨ Z) → A ∨ B ∨ D ∨ E ∨ F ∨ G := by
  intros h₁ h₂
  R1 h₁, h₂, (W ∨ Z)

