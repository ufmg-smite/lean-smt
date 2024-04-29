/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruct.Options
import Smt.Reconstruct.Prop.LiftOrNToImp
import Smt.Reconstruct.Prop.Pull
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Prop

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

def resolutionCoreMeta (val₁ val₂ pivot : Expr) (sufIdx₁' sufIdx₂' : Option Nat)
    (flipped : Bool) : MetaM Expr := do
  let type₁ ← inferType val₁
  let type₂ ← inferType val₂
  let mut pivot := pivot
  let mut notPivot := mkApp (mkConst ``Not) pivot
  let sufIdx₁ ←
    match sufIdx₁' with
    | none   => pure $ (← getLength type₁) - 1
    | some i => pure i
  let sufIdx₂ ←
    match sufIdx₂' with
    | none   => pure $ (← getLength type₂) - 1
    | some i => pure i
  let len₁ := sufIdx₁ + 1
  let len₂ := sufIdx₂ + 1
  let lenGoal := len₁ + len₂ - 2
  let prefixLength := len₁ - 2
  if flipped then
    let tmp := pivot
    pivot := notPivot
    notPivot := tmp
  let pulled₁ ← pullCore pivot val₁ type₁ sufIdx₁'
  let pulled₂ ← pullCore notPivot val₂ type₂ sufIdx₂'
  let props₁ ← collectPropsInOrChain' sufIdx₁ type₁
  let props₁ := props₁.erase pivot
  let props₂ ← collectPropsInOrChain' sufIdx₂ type₂
  let props₂ := props₂.erase notPivot
  let props := props₁ ++ props₂
  let thmName : Name :=
    match Nat.blt 1 len₁, Nat.blt 1 len₂ with
    | true, true   => if flipped then ``flipped_resolution_thm  else ``resolution_thm
    | true, false  => if flipped then ``flipped_resolution_thm₃ else ``resolution_thm₃
    | false, true  => if flipped then ``flipped_resolution_thm₂ else ``resolution_thm₂
    | false, false => if flipped then ``flipped_resolution_thm₄ else ``resolution_thm₄
  let mut answer ← mkAppM thmName #[pulled₁, pulled₂]
  if lenGoal > prefixLength + 1 then
    let lemmas ← ungroupPrefixLemmas props prefixLength
    for l in lemmas do
      answer := mkApp l answer
  return answer

syntax (name := resolution_1) "R1" ident "," ident "," term (",")? ("[" term,* "]")? : tactic
syntax (name := resolution_2) "R2" ident "," ident "," term (",")? ("[" term,* "]")? : tactic

def parseResolution : Syntax → TacticM (Option Nat × Option Nat)
  | `(tactic| R1 $_, $_, $_, [ $[$hs],* ]) => get hs
  | `(tactic| R1 $_, $_, $_)               => pure (none, none)
  | `(tactic| R2 $_, $_, $_, [ $[$hs],* ]) => get hs
  | `(tactic| R2 $_, $_, $_)               => pure (none, none)
  | _ => throwError "[Resolution]: wrong usage"
where
  get (hs : Array Term) : TacticM (Option Nat × Option Nat) :=
    match hs.toList with
      | [n₁, n₂] => do
        let e₁ ← elabTerm n₁ none
        let e₂ ← elabTerm n₂ none
        return (getNatLit? e₁, getNatLit? e₂)
      | _ => throwError "[Resolution]: wrong usage"

def r₀ (mv : MVarId) (e₁ e₂ pivot : Expr) (i₁ i₂ : Option Nat) : MetaM Unit := do
  let answer ← resolutionCoreMeta e₁ e₂ pivot i₁ i₂ false
  mv.assign answer

def r₁ (mv : MVarId) (e₁ e₂ pivot : Expr) (i₁ i₂ : Option Nat) : MetaM Unit := do
  let answer ← resolutionCoreMeta e₁ e₂ pivot i₁ i₂ true
  mv.assign answer

@[tactic resolution_1] def evalResolution_1 : Tactic := fun stx =>
  withMainContext do
    trace[smt.profile.reconstruct] m!"[resolution_1] start time: {← IO.monoNanosNow}ns"
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    let (sufIdx₁, sufIdx₂) ← parseResolution stx
    let val₁ ← elabTerm firstHyp none
    let val₂ ← elabTerm secondHyp none
    let pivot ← elabTerm pivotTerm none
    let answer ← resolutionCoreMeta val₁ val₂ pivot sufIdx₁ sufIdx₂ false
    let mvar ← getMainGoal
    let type ← inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[resolution_1] end time: {← IO.monoNanosNow}ns"

@[tactic resolution_2] def evalResolution_2 : Tactic := fun stx =>
  withMainContext do
    trace[smt.profile.reconstruct] m!"[resolution_2] start time: {← IO.monoNanosNow}ns"
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    let (sufIdx₁, sufIdx₂) ← parseResolution stx
    let val₁ ← elabTerm firstHyp none
    let val₂ ← elabTerm secondHyp none
    let pivot ← elabTerm pivotTerm none
    let answer ← resolutionCoreMeta val₁ val₂ pivot sufIdx₁ sufIdx₂ true
    let mvar ← getMainGoal
    let type ← inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[resolution_2] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruct.Prop
