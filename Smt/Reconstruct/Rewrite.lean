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

open Lean Elab Meta
open Smt.Reconstruct.Prop

def simpLocalDeclRw (mv : MVarId) (fv : FVarId) (rule : Expr) : MetaM (FVarId × MVarId) := do
  let simpTheorems ← ({} : SimpTheorems).add (Origin.other `h) #[] rule
  let simpTheorems : SimpTheoremsArray := #[simpTheorems]
  let (some (fv, mv), _) ← Meta.simpLocalDecl mv fv {simpTheorems }
    | throwError "Simp did not work"
  return (fv, mv)

def simpTargetRw (mv : MVarId) (rule : Expr) : MetaM MVarId := do
  let simpTheorems ← ({} : SimpTheorems).add (Origin.other `h) #[] rule
  let simpTheorems : SimpTheoremsArray := #[simpTheorems]
  let (some mv, _) ← Meta.simpTarget mv {simpTheorems }
    | throwError "Simp did not work"
  return mv

def traceSmtRw (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def smtRw (mv : MVarId) (op : Expr) (assoc : Expr) (null : Expr) (nullr1 : Expr) (nullr2 : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit :=
  withTraceNode `smt.reconstruct.smtRw traceSmtRw do
  let n := arr.size
  let mut mv' := mv
  mv' ← mv'.assert `null' (← Meta.inferType null) null
  let (fv1, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  mv' ← mv'.assert (← mkFreshUserName `h1) (mkAppN (.const `Eq [.zero]) #[Expr.sort Lean.Level.zero, .fvar fv1, null]) (mkAppN (.const `rfl [.succ .zero]) #[Expr.sort Lean.Level.zero, .fvar fv1])
  let (fv3, mv'') ← mv'.intro1P
  mv' := mv''
  mv' ← (mv'.assert (← mkFreshUserName `h2) (← Meta.inferType nullr2) nullr2)
  let (fv4, mv'') ← mv'.intro1P
  mv' := mv''
  mv' ← (mv'.assert (← mkFreshUserName `h) (← Meta.inferType nullr1) nullr1)
  let (fv2, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  let mut fv2 := fv2
  let r ← mv'.rewrite (← fv2.getType) (.fvar fv3) true
  let res ← mv'.replaceLocalDecl fv2 r.eNew r.eqProof
  mv' := res.mvarId
  fv2 := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let mut fv4 := fv4
  let r ← mv'.rewrite (← fv4.getType) (.fvar fv3) true
  let res ← mv'.replaceLocalDecl fv4 r.eNew r.eqProof
  mv' := res.mvarId
  fv4 := res.fvarId
  mv'.withContext do
  let mut mv' := mv'
  let fv2 := (res.subst.get fv2).fvarId!
  let mut arr2 : Array Expr := #[]
  for i in [: n] do
    let m := arr[i]!.size
    if m == 0 then
      arr2 := Array.push arr2 (.fvar fv1)
    if m == 1 then
      arr2 := Array.push arr2 arr[i]![0]!
    if m > 1 then
      let mut term := arr[i]![m-1]!
      for j in [: m-1] do
        term := mkAppN op #[arr[i]![m-j-2]!, term]
        if let some r ← observing? (mv'.rewrite (← mv'.getType) (mkAppN assoc #[arr[i]![m-j-2]!]) true) then
          mv' ← mv'.replaceTargetEq r.eNew r.eqProof
      arr2 := Array.push arr2 term
  let rule' :=  mkAppN rule arr2
  mv' ← (mv'.assert (← mkFreshUserName `h4) (← Meta.inferType rule') rule')
  let (fv, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv2)
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv4)
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  mv' ← simpTargetRw mv' nullr1
  if let some r ← observing? (mv'.rewrite (← mv'.getType) (.fvar fv)) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  for i in [: n] do
    let m := arr[i]!.size
    for j in [: m-1] do
      if let some r ← observing? (mv'.rewrite (← mv'.getType) (.app assoc arr[i]![j]!)) then
        mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  mv'.refl

syntax inner := "[" term,* "]"
syntax outer := "[" inner,* "]"

syntax (name := smt_rw) "smt_rw" ident ident ident ident ident ident outer : tactic

open Tactic in
def parseInner : TSyntax ``inner → TacticM (Array Expr)
  | `(inner| [$ts,*]) => ts.getElems.mapM (elabTerm · none)
  | _ => throwError "[inner]: wrong usage"

open Tactic in
def parseOuter : TSyntax ``outer → TacticM (Array (Array Expr))
  | `(outer| [$is,*]) => is.getElems.mapM parseInner
  | _ => throwError "[outer]: wrong usage"

open Tactic in
@[tactic smt_rw] def evalSMTRw : Tactic := fun stx => do
  let mv : MVarId ← getMainGoal
  let rr ← elabTermForApply stx[6]
  let xs ← parseOuter ⟨stx[7]⟩
  let as  ← elabTermForApply stx[2]
  let nu ← elabTerm stx[3] none
  let nur  ← elabTermForApply stx[4]
  let nur2  ← elabTermForApply stx[5]
  let opr ← elabTerm stx[1] none
  smtRw mv opr as nu nur nur2 rr xs


example : ((True ∧ p4) = (p4)) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[], [p4]]

example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw Or or_assoc_eq False or_false false_or bool_or_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw Or or_assoc_eq False or_false false_or bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]

example : (p1 ∧ p2 ∧ p3 ∧ p4 ∧ True) = (p1 ∧ p2 ∧ p3 ∧ p4) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[p1, p2, p3, p4], []]

example : (p1 ∧ True) = p1 := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[p1], []]

example : (True ∧ p1) = p1 := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[], [p1]]

end Smt.Reconstruct.Tactic
