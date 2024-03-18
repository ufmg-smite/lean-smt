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

theorem or_true' : (p ∧ True') = p := by simp [True']

theorem true'_or : (True' ∧ p) = p := by simp [True']

def smtRw (mv : MVarId) (op : Expr) (assoc : Expr) (null : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit := do
  let n := arr.size
  let mut mv' := mv
  let mut arr2 : Array Expr := #[]
  for i in [: n] do
    let m := arr[i]!.size
    if m == 0 then
      arr2 := Array.push arr2 (.const ``True' [])
    if m == 1 then
      arr2 := Array.push arr2 arr[i]![0]!
    if m > 1 then
      let mut term := arr[i]![m-1]!
      for j in [: m-1] do
        term := mkAppN op #[arr[i]![m-j-2]!, term]
        if let some r ← observing? (mv'.rewrite (← mv'.getType) (mkAppN assoc #[arr[i]![m-j-2]!]) true) then
          mv' ← mv'.replaceTargetEq r.eNew r.eqProof
      arr2 := Array.push arr2 term
  logInfo m!"{arr2}"
  let rule' :=  mkAppN rule arr2
  logInfo m!"{rule}"
  logInfo m!"{← Meta.inferType rule}"
  logInfo m!"{rule'}"
  mv' ← (mv'.assert (← mkFreshUserName `h) (← Meta.inferType rule') rule')
  let (fv, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  if let some r ← observing? (mv'.rewrite (← fv.getType) (.const ``and_true' [])) then
    let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
    mv' := res.mvarId
    fv := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  if let some r ← observing? (mv'.rewrite (← fv.getType) (.const ``and_true' [])) then
    let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
    mv' := res.mvarId
    fv := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  if let some r ← observing? (mv'.rewrite (← fv.getType) (.const ``true'_and [])) then
    let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
    mv' := res.mvarId
    fv := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  if let some r ← observing? (mv'.rewrite (← fv.getType) (.const ``true'_and [])) then
    let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
    mv' := res.mvarId
    fv := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  if let some r ← observing? (mv'.rewrite (← mv'.getType) null) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) null) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) null) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  logInfo m!"{mv'}"
  if let some r ← observing? (mv'.rewrite (← mv'.getType) (.fvar fv)) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  -- if let some r ← observing? (mv'.rewrite (← mv'.getType) rule) then
  --   mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  logInfo m!"{mv'}"
  for i in [: n] do
    let m := arr[i]!.size
    for j in [: m-1] do
      if let some r ← observing? (mv'.rewrite (← mv'.getType) (.app assoc arr[i]![j]!)) then
        mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  mv'.refl

syntax inner := "[" term,* "]"
syntax outer := "[" inner,* "]"

#check FVarId.getType

syntax (name := smt_rw) "smt_rw" ident ident ident ident outer : tactic

def parseInner : TSyntax ``inner → TacticM (Array Expr)
  | `(inner| [$ts,*]) => ts.getElems.mapM (elabTerm · none)
  | _ => throwError "[inner]: wrong usage"

def parseOuter : TSyntax ``outer → TacticM (Array (Array Expr))
  | `(outer| [$is,*]) => is.getElems.mapM parseInner
  | _ => throwError "[outer]: wrong usage"

@[tactic smt_rw] def evalSMTRw : Tactic := fun stx => do
  let mv : MVarId ← getMainGoal
  let rr ← elabTermForApply stx[4]
  let xs ← parseOuter ⟨stx[5]⟩
  let as  ← elabTermForApply stx[2]
  let nu  ← elabTermForApply stx[3]
  let opr ← elabTerm stx[1] none
  smtRw mv opr as nu rr xs

example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  --have := @bool_and_flatten (x1 ∧ x2 ∧ x3) b (y1 ∧ y2) (z1 ∧ z2)
  -- rw [← @and_assoc x2]
  -- rw [← @and_assoc x1]
  -- rw [← @and_assoc y1]
  -- rw [← @and_assoc z1]
  -- rw [and_true, and_true]
  -- rw [this]
  smt_rw And and_assoc_eq and_true bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]


example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw Or or_assoc_eq or_false bool_or_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw Or or_assoc_eq or_false bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]




def twoAnd:= (mkAppN (.const `And []) #[.const `True [],.const `False []])

def threeAnd := (mkAppN (.const `And []) #[twoAnd, .const `False []])

#check List.toArray
#check List.cons

elab "threeAnd" : term => return threeAnd

#reduce threeAnd

#check MVarId.assert

example : (p1 ∧ p2 ∧ True) = (p1 ∧ p2) := by
  --smt_rw and_assoc_eq and_true bool_and_true [[p1], [True']]
  rw [← and_assoc]
  have := @bool_and_true (p1 ∧ p2) True'
  rw [and_true'] at this
  rw [this]
  rw [and_true']

example : (p1 ∧ p2 ∧ p3 ∧ p4 ∧ True) = (p1 ∧ p2 ∧ p3 ∧ p4) := by
  smt_rw And and_assoc_eq and_true bool_and_true [[p1, p2, p3, p4], []]






example : (True ∧ p1) = p1 := by
  -- have := @bool_and_true True' p1
  -- rw [true'_and, true'_and] at this
  -- rw [this]

  smt_rw And and_assoc_eq and_true bool_and_true [[], [p1]]

example : (p1 ∧ True) = p1 := by
  -- have := @bool_and_true p1 True'
  -- rw [and_true', and_true'] at this
  -- rw [this]

  smt_rw And and_assoc_eq and_true bool_and_true [[p1], []]



-- Smt.Reconstruct.Prop.bool_and_true {xs ys : Prop} : (xs ∧ True ∧ ys) = (xs ∧ ys)

-- use a new True: True'
-- instantiate the base lemma with True' whenever a list is empty

end Smt.Reconstruct.Tactic
