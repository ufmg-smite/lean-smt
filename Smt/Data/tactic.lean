/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Lean
import Std
import Aesop
import Smt.Data.BitVec

open Lean Elab.Tactic Meta Expr Syntax

namespace Smt.Data.tactic

theorem and_assoc_eq : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := by simp [and_assoc]

theorem or_assoc_eq : ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := by simp [or_assoc]

theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := by
  rw [← @and_assoc b ys zs]

theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs) := by
  rw [← @or_assoc b ys zs]

theorem bool_and_false : (xs ∧ False ∧ ys) = False := by rw [false_and, and_false]

theorem bool_and_true : (xs ∧ True ∧ ys) = (xs ∧ ys) := by rw [true_and]

theorem bool_and_dup : (xs ∧ b ∧ ys ∧ b ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := by aesop

theorem bool_or_dup : (xs ∨ b ∨ ys ∨ b ∨ zs) = (xs ∨ b ∨ ys ∨ zs) := by aesop

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

example : (p1 ∧ True) = p1 := by
  smt_rw and_assoc_eq and_true bool_and_true [[p1], []]

  example : (True ∧ p1) = p1 := by
    smt_rw and_assoc_eq true_and bool_and_true [[p1], []]
