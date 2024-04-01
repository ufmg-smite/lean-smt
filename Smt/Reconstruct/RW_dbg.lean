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

def True' := True

theorem and_true' : (p ∧ True') = p := by simp [True']

theorem true'_and : (True' ∧ p) = p := by simp [True']

theorem or_true' : (p ∧ True') = p := by simp [True']

theorem true'_or : (True' ∧ p) = p := by simp [True']

#check MVarId.define

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


instance : ToString FVarId := ⟨fun fv => fv.name.toString⟩

#check @rfl Prop True
#check @Eq Prop True True'

example : @Eq Prop True True' := @rfl Prop True'

def myExpr : Expr := mkAppN (.const `Eq [.zero]) #[Expr.sort Lean.Level.zero, .const `True' [], (.const `True [])]

def myExpr1 : Expr := mkAppN (.const `rfl [.zero]) #[Expr.sort Lean.Level.zero, .const `True []]

elab "myExpr" : term => return myExpr
elab "myExpr1" : term => return myExpr1


#check @Eq.{1} Prop True True
#check Eq

def smtRw (mv : MVarId) (op : Expr) (assoc : Expr) (null : Expr) (nullr1 : Expr) (nullr2 : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit := do
  let n := arr.size
  let mut mv' := mv
  mv' ← mv'.assert `null' (← Meta.inferType null) null
  let (fv1, mv'') ← mv'.intro1P
  mv' := mv''
  mv'.withContext do
  let mut mv' := mv'
  logInfo m!"{← Meta.inferType null}"
  logInfo m!"{Expr.fvar fv1}"
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
  logInfo m!"fv2 before: {Expr.fvar fv2}"
  let mut mv' := mv'
  let mut fv4 := fv4
  let r ← mv'.rewrite (← fv4.getType) (.fvar fv3) true
  logInfo m!"mv' before: {mv'}"
  let res ← mv'.replaceLocalDecl fv4 r.eNew r.eqProof
  logInfo m!"r.enew: {r.eNew}"
  mv' := res.mvarId
  fv4 := res.fvarId
  logInfo m!"fv2 here: {Expr.fvar fv2}"
  logInfo m!"null: {mv'}"
  mv'.withContext do
  let mut mv' := mv'
  let fv2 := (res.subst.get fv2).fvarId!
  logInfo m!"subs: {res.subst.get fv2}"
  logInfo m!"fv2 after here: {Expr.fvar fv2}"



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
  logInfo m!"arr2 : {arr2}"

  let rule' :=  mkAppN rule arr2
  logInfo m!"Rule : {rule}"
  logInfo m!"{← Meta.inferType rule}"
  logInfo m!"{rule'}"
  mv' ← (mv'.assert (← mkFreshUserName `h4) (← Meta.inferType rule') rule')
  let (fv, mv'') ← mv'.intro1P
  mv' := mv''

  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv2)
  logInfo m!"now1: {mv'}"
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  (fv, mv') ← simpLocalDeclRw mv' fv (.fvar fv4)
  logInfo m!"now2: {mv'}"
  -- mv'.withContext do
  -- logInfo m!"fv2 after: {Expr.fvar fv2}"
  -- let mut mv' := mv'
  -- let mut fv := fv
  -- logInfo m!"fv2: {Expr.fvar fv2}"
  -- if let some r ← observing? (mv'.rewrite (← fv.getType) (.fvar fv2)) then
  --   logInfo m!"fv2': {Expr.fvar fv2}"
  --   let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
  --   mv' := res.mvarId
  --   fv := res.fvarId

  -- mv'.withContext do
  -- let mut mv' := mv'
  -- let mut fv := fv
  -- if let some r ← observing? (mv'.rewrite (← fv.getType) (.fvar fv2)) then
  --   let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
  --   mv' := res.mvarId
  --   fv := res.fvarId
  -- logInfo m!"now2: {mv'}"
  -- mv'.withContext do
  -- let mut mv' := mv'
  -- let mut fv := fv
  -- if let some r ← observing? (mv'.rewrite (← fv.getType) (.fvar fv4)) then
  --   let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
  --   mv' := res.mvarId
  --   fv := res.fvarId
  -- logInfo m!"now3: {mv'}"
  -- logInfo m!"fv4: {Expr.fvar fv4}"
  -- mv'.withContext do
  -- let mut mv' := mv'
  -- let mut fv := fv
  -- if let some r ← observing? (mv'.rewrite (← fv.getType) (.fvar fv4)) then
  --   let res ← mv'.replaceLocalDecl fv r.eNew r.eqProof
  --   mv' := res.mvarId
  --   fv := res.fvarId
  -- logInfo m!"now4: {mv'}"
  mv'.withContext do
  let mut mv' := mv'
  let mut fv := fv
  mv' ← simpTargetRw mv' nullr1

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

#check @rfl Prop

example : ((True ∧ p3) = (p3)) := by
  -- have ⟨True'', hTrue''⟩ : ∃ (p :Prop), p = True := sorry
  -- let True'' : Prop := True
  -- have h2 : True'' = True := rfl
  -- have : ∀ p : Prop, (True ∧ p) = p := sorry
  -- rewrite [← h2] at this
  -- have H := @bool_and_true True'' p1
  -- simp only [this] at H
  -- --rw (config := {occs := .all}) [this] at H
  -- --rewrite [this] at H
  -- sorry

  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[], [p3]]
  -- sorry


example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  -- have := @bool_and_flatten (x1 ∧ x2 ∧ x3) b (y1 ∧ y2) (z1 ∧ z2)
  -- rw [← @and_assoc x2]
  -- rw [← @and_assoc x1]
  -- rw [← @and_assoc y1]
  -- rw [← @and_assoc z1]
  -- rw [and_true, and_true]
  -- rw [this]
  smt_rw And and_assoc_eq True and_true true_and bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]


example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw Or or_assoc_eq False or_false false_or bool_or_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And and_assoc_eq True and_true true_and bool_and_dup [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw Or or_assoc_eq False or_false false_or bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]




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
  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[p1, p2, p3, p4], []]




#check @rfl Prop




example : (p1 ∧ True) = p1 := by

  have ⟨p, hp⟩: ∃ (p : Prop), p = True := ⟨True, rfl⟩
  -- have := @bool_and_true p1 True'
  -- rw [and_true', and_true'] at this
  -- rw [this]

  smt_rw And and_assoc_eq True and_true true_and bool_and_true [[p1], []]



example : (True ∧ p1) = p1 := by
  have := @bool_and_true True' p1
  rw [true'_and, true'_and] at this
  -- rw [this]
  sorry


example : (p1 ∧ True) = p1 := by
  -- have := @bool_and_true p1 True'
  -- rw [and_true', and_true'] at this
  -- rw [this]
  sorry

-- Smt.Reconstruct.Prop.bool_and_true {xs ys : Prop} : (xs ∧ True ∧ ys) = (xs ∧ ys)

-- use a new True: True'
-- instantiate the base lemma with True' whenever a list is empty



/- ### Improvements-/
-- Use `MVarId.replace` instead of `MVarId.replaceLocalDecl`
-- Use `simp only` instead of rewriting a bunch


  -- let simpTheorems ← ({} : SimpTheorems).addConst `eq_self
  -- let simpTheorems : SimpTheoremsArray := #[simpTheorems]
  -- _ ← simpLocalDecl mv fv {simpTheorems } #[]


end Smt.Reconstruct.Tactic
