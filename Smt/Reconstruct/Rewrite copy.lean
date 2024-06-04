/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Lean

import Smt.Reconstruct.Prop.Rewrites

namespace Smt.Reconstruct.Tactic

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

-- USE assertHypotheses INSTEAD

def smtRw (mv : MVarId) (op : Expr) (assoc : Expr) (id : Expr) (id_op : Expr) (op_id : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit :=
  withTraceNode `smt.reconstruct.smtRw traceSmtRw do
  let n := arr.size
  let mut mv' := mv
  mv' ← mv'.assert `null' (← Meta.inferType id) id
  let (fv1, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  mv' ← mv'.assert (← mkFreshUserName `h1) (mkAppN (.const `Eq [.zero]) #[Expr.sort Lean.Level.zero, .fvar fv1, id]) (mkAppN (.const `rfl [.succ .zero]) #[Expr.sort Lean.Level.zero, .fvar fv1])
  let (fv3, mv'') ← mv'.intro1P
  mv' := mv''
  mv' ← (mv'.assert (← mkFreshUserName `h2) (← Meta.inferType id_op) id_op)
  let (fv4, mv'') ← mv'.intro1P
  mv' := mv''
  mv' ← (mv'.assert (← mkFreshUserName `h) (← Meta.inferType op_id) op_id)
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
      arr2 := Array.push arr2 term
  let rule' :=  mkAppN rule arr2
  mv' ← (mv'.assert (← mkFreshUserName `h5) (← Meta.inferType rule') rule')
  let (fv, mv'') ← mv'.intro1P
  mv' := mv''
  logInfo m!"{mv'}"
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv2)
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv4)
  let (lhs, _) ← Tactic.Conv.getLhsRhsCore mv'
  logInfo m!"{mv'}"
  let some (_, lhs2, _) ←  matchEq? (← Meta.inferType (.fvar fv))| throwError "invalid rule"
  let rule1 :=  mkAppN (.const `Eq [.succ .zero]) #[Expr.sort Lean.Level.zero, lhs, lhs2]
  let mv1 ← mkFreshExprMVar rule1
  mv' ← (mv'.assert (← mkFreshUserName `h4) rule1 mv1)
  let (fv5, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  let r ← mv'.rewrite (← mv'.getType) (.fvar fv5)
  logInfo m!"{mv'}"
  mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) (.fvar fv)) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  AC.rewriteUnnormalized mv'
  logInfo m!"{mv'}"
  let mut mv1 := mv1
  mv1 ← instantiateMVars mv1
  logInfo m!"{mv1}"
  mv1.mvarId!.withContext do
  AC.rewriteUnnormalized mv1.mvarId!


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




example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2) ∧ z1 ∧ z2) = ((x1 ∧ x2 ∧ x3) ∧ (b ∧ (y1 ∧ y2)) ∧ (z1 ∧ z2)) := by
  sorry
example : (True ∧ p4) = (p4) := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_true [[], [p4]]

#check bool_and_flatten

example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by

  -- smt_rw And and_assoc_eq True true_and and_true bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

  have : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = ((x1 ∧ x2 ∧ x3) ∧ (b ∧ (y1 ∧ y2 ∧ True)) ∧ (z1 ∧ z2 ∧ True)) := by
    ac_rfl
  rw [this]
  rw [@bool_and_flatten (x1 ∧ x2 ∧ x3) b (y1 ∧ y2 ∧ True) (z1 ∧ z2 ∧ True)]
  ac_rfl


#check Tactic.getMainGoal

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2, True]]
  -- rw [and_true]
  -- have : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2) = ((x1 ∧ x2 ∧ x3) ∧ b ∧ (y1 ∧ y2) ∧ b ∧ (z1 ∧ z2)) := by
  --   ac_rfl
  -- rw [this]
  -- rw [@bool_and_dup (x1 ∧ x2 ∧ x3) b (y1 ∧ y2) (z1 ∧ z2)]
  -- ac_rfl

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw Or or_assoc_eq False false_or or_false bool_or_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2, False]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw Or or_assoc_eq False false_or or_false bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]

example : (p1 ∧ p2 ∧ p3 ∧ p4 ∧ True) = (p1 ∧ p2 ∧ p3 ∧ p4) := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_true [[p1, p2, p3, p4], []]

example : (p1 ∧ True) = p1 := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_true [[p1], []]

example : (True ∧ p1) = p1 := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_true [[], [p1]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True true_and and_true bool_and_dup [[x1, x2, x3], [b], [], [z1, z2]]


end Smt.Reconstruct.Tactic
