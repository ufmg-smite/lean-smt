/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Lean

import Smt.Reconstruct.Prop.Rewrites

namespace Smt.Reconstruct.Tactic

open Lean Elab.Tactic
open Smt.Reconstruct.Prop

def True' := True

theorem and_true' : (p ∧ True') = p := by simp [True']

theorem true'_and : (True' ∧ p) = p := by simp [True']

def smtRw (mv : MVarId) (assoc : Expr) (null : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit := do
  let n := arr.size
  let mut mv' := mv
  for i in [: n] do
    let m := arr[i]!.size
    if m > 1 then
      for j in [: m-1] do
        if let some r ← observing? (mv'.rewrite (← mv'.getType) (mkAppN assoc #[arr[i]![m-j-2]!]) true) then
          mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) rule) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) null) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  for i in [: n] do
    let m := arr[i]!.size
    for j in [: m-1] do
      if let some r ← observing? (mv'.rewrite (← mv'.getType) (.app assoc arr[i]![j]!)) then
        mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  mv'.refl

syntax inner := "[" term,* "]"
syntax outer := "[" inner,* "]"

syntax (name := smt_rw) "smt_rw" ident ident ident outer : tactic

def parseInner : TSyntax ``inner → TacticM (Array Expr)
  | `(inner| [$ts,*]) => ts.getElems.mapM (elabTerm · none)
  | _ => throwError "[inner]: wrong usage"

def parseOuter : TSyntax ``outer → TacticM (Array (Array Expr))
  | `(outer| [$is,*]) => is.getElems.mapM parseInner
  | _ => throwError "[outer]: wrong usage"

@[tactic smt_rw] def evalSMTRw : Tactic := fun stx => do
  let mv : MVarId ← getMainGoal
  let rr ← elabTerm stx[3] none
  let xs ← parseOuter ⟨stx[4]⟩
  let op  ← elabTermForApply stx[1]
  let nu  ← elabTermForApply stx[2]
  smtRw mv op nu rr xs

example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw and_assoc_eq and_true bool_and_flatten [[x1, x2], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [b], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw or_assoc_eq or_false bool_or_dup [[x1, x2, x3], [b], [y1, y2], [b], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [b], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw or_assoc_eq or_false bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]



example : (p1 ∧ p2 ∧ True) = (p1 ∧ p2) := by
  --smt_rw and_assoc_eq and_true bool_and_true [[p1], [True']]
  rw [← and_assoc]
  have := @bool_and_true (p1 ∧ p2) True'
  rw [and_true'] at this
  rw [this]
  rw [and_true']






-- #check true_and

-- example : (True ∧ p1) = p1 := by
--   smt_rw and_assoc_eq and_true bool_and_true [[], [p1]]



-- Smt.Reconstruct.Prop.bool_and_true {xs ys : Prop} : (xs ∧ True ∧ ys) = (xs ∧ ys)

-- use a new True: True'
-- instantiate the base lemma with True' whenever a list is empty

end Smt.Reconstruct.Tactic
