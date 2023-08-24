/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Lean
import Std
import Aesop

open Lean Elab.Tactic Meta Expr Syntax 


namespace Smt.Data.tactic

-- (@ t1 (and cvc.zs true)
-- (@ t2 (=> cvc.xs cvc.ys)
-- (@ t3 (and cvc.xs (and t2 (and cvc.s (and cvc.ys t1))))
-- (@ t4 (and cvc.ys true)
-- (@ t5 (and cvc.xs (and t2 (and (and cvc.s t4) t1)))
-- (# a0 (holds (distinct t5 t3))
-- (: (holds false)
-- (dsl.bool-and-flatten (and cvc.xs (and t2 true)) cvc.s t4 t1 _ ))

#check and_assoc
#check and_rotate


theorem and_assoc_eq : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := by simp [and_assoc]

theorem or_assoc_eq : ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := by simp [or_assoc]

theorem and_assoc' : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c  := by aesop

theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := by
  rw [← @and_assoc b ys zs]

theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs) := by
  rw [← @or_assoc b ys zs]
  
theorem bool_and_false : (xs ∧ False ∧ ys) = False := by
  rw [false_and, and_false]

theorem bool_and_true : (xs ∧ True ∧ ys) = (xs ∧ ys) := by
  rw [true_and]

theorem bool_and_dup : (xs ∧ b ∧ ys ∧ b ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := by 
  rw [← @and_assoc ys b zs]
  rw [← @and_assoc b _ zs]
  rw [@and_comm ys b]
  rw [← @and_assoc b b ys]
  rw [and_self]
  rw [and_assoc]


theorem bool_or_dup : (xs ∨ b ∨ ys ∨ b ∨ zs) = (xs ∨ b ∨ ys ∨ zs) := by aesop


-- def countArgs (a b : Prop): Expr := mkAppN (.const `And []) #[a.toExpr, b.toExpr]

-- variable {a b c : Prop}
-- #check mkPropExt
-- #eval countArgs True True
#check getAppNumArgs
#check Expr.eq?
def x_and_x : Expr :=
  .forallE `x (mkSort levelZero) (mkAppN (.const `And []) #[.bvar 0, .bvar 0]) BinderInfo.default


def getNumArgsFn (e : Expr) (f : Expr) : MetaM Nat := do
  let mut arg := e
  let mut count := 0
  while arg.isAppOf (constName! f) do
    arg := arg.getAppArgs[1]!
    count := count + 1
  return count

#check Expr.isAppOf

def smtSimp (mv : MVarId) (f : Expr) (null : Expr): MetaM Unit := do
  let tp ← mv.getType
  let mut arg := tp.getAppArgs[1]!
  let mut arg0 := tp.getAppArgs[0]!
  while arg.isApp do
    arg := arg.getAppArgs[1]!
    if (arg.getAppArgs[0]!).isAppOf (constName! f) then
      arg0 := arg.getAppArgs[0]!
      break
  logInfo m!"{arg0}"
  let c ← getNumArgsFn arg0 f
  let mut mv' := mv
  for _ in [: c - 1] do
    let r ← mv'.rewrite (← mv'.getType) (.const ``bool_and_flatten [])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  let r ← mv'.rewrite (← mv'.getType) (.const ``and_true [])
  mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  mv'.refl

syntax (name := smt_simpp) "smt_simpp" term : tactic

@[tactic smt_simpp] def SMTSimp : Tactic := fun stx => do
  let mv : MVarId ← Elab.Tactic.getMainGoal
  smtSimp mv (← elabTerm stx[1] none) (← elabTerm stx[2] none)
  Elab.Tactic.replaceMainGoal [mv]



example : (xs ∧ (xs → ys) ∧ (s ∧ ys ∧ True) ∧ zs ∧ True) = (xs ∧ (xs → ys) ∧ s ∧ ys ∧ zs ∧ True) := by
  rw [bool_and_flatten]
  rw [and_true]

example : (xs ∧ (xs → ys) ∧ (s ∧ ys ∧ True) ∧ zs ∧ True) = (xs ∧ (xs → ys) ∧ s ∧ ys ∧ zs ∧ True) := by
  rw [and_true]
  rw [← @and_assoc s ys (zs ∧ True)]

example : (xs ∧ (xs → ys) ∧ (s ∧ ys ∧ True) ∧ zs ∧ True) = (xs ∧ (xs → ys) ∧ s ∧ ys ∧ zs ∧ True) := by
  rw [@and_assoc s (ys ∧ True) (zs ∧ True)]
  rw [and_true]

example : (x1 ∧ x2 ∧ x3 ∧ (s ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) = 
          (x1 ∧ x2 ∧ x3 ∧ s ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) := by
  rw [bool_and_flatten]
  rw [bool_and_flatten]
  rw [and_true]

example : (x1 ∧ x2 ∧ x3 ∧ False ∧ y1 ∧ y2 ∧ True) = False := by
  rw [bool_and_false]
  rw [and_false, and_false]

example : (xs ∧ False ∧ y1 ∧ y2) = False := by
  rw [bool_and_false]

example : (x1 ∧ x2 ∧ False ∧ y1 ∧ y2) = False := by
  rw [bool_and_false, and_false]

example : (xs ∧ (b ∧ y1 ∧ y2) ∧ z1 ∧ z2 ∧ z3) = (xs ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ z3) := by
  rw [bool_and_flatten, bool_and_flatten]

example : (x1 ∧ x2 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  rw [← @and_assoc x1 x2 _]
  rw [← @and_assoc y1 _ _]
  rw [← @and_assoc z1 _ _]
  rw [bool_and_flatten]
  rw [and_true]
  rw [and_true]
  rw [and_assoc]
  rw [and_assoc]

example : (x1 ∧ x2 ∧ False ∧ z1 ∧ z2 ∧ z3 ∧ True) = False := by
  rw [← @and_assoc x1 x2 _]
  rw [bool_and_false]

example : (x1 ∧ x2 ∧ True ∧ z1 ∧ z2 ∧ z3 ∧ True) = (x1 ∧ x2 ∧ z1 ∧ z2 ∧ z3 ∧ True) := by
  rw [← @and_assoc x1 x2 _]
  rw [bool_and_true]
  rw [and_assoc]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  rewrite [← @and_assoc x2]
  rw [← @and_assoc x1]
  rw [← @and_assoc y1]
  rw [bool_and_dup]
  rw [@and_assoc x1 _ _]
  rw [@and_assoc x2 _ _]
  rw [@and_assoc y1 _ _]

-- write a tactic that proves this theorem using bool-and-flatten which is already in Prop.lean

example : (xs ∧ (xs → ys) ∧ (s ∧ ys ∧ True) ∧ zs ∧ True) = (xs ∧ (xs → ys) ∧ s ∧ ys ∧ zs ∧ True) := by
  smt_simpp And

example : (x1 ∧ x2 ∧ x3 ∧ (s ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) = 
          (x1 ∧ x2 ∧ x3 ∧ s ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) := by
  smt_simpp And

example : (x1 ∧ (x2 ∨ x3) ∧ (s ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) = 
          (x1 ∧ (x2 ∨ x3) ∧ s ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ z3 ∧ z4 ∧ True) := by
  smt_simpp And

#check mkAppN
def opAssoc (op : Name) : Expr :=
  Expr.lam `p (.sort Level.zero) (.lam `q (.sort Level.zero) (.lam `r (.sort Level.zero)
    (mkAppN (.const ``Iff []) #[mkAppN (.const op []) #[mkAppN (.const op []) #[.bvar 2, .bvar 1], .bvar 0], 
                            mkAppN (.const op []) #[.bvar 2, mkAppN (.const op []) #[.bvar 1, .bvar 0]]]) BinderInfo.default) BinderInfo.default) BinderInfo.default

def opAssoc' (op : Name) : Expr :=
  Expr.lam `p (.sort Level.zero) (.lam `q (.sort Level.zero) (.lam `r (.sort Level.zero)
    (mkAppN (.const ``Iff []) #[mkAppN (.const op []) #[.bvar 2, mkAppN (.const op []) #[.bvar 1, .bvar 0]], 
                                mkAppN (.const op []) #[mkAppN (.const op []) #[.bvar 2, .bvar 1], .bvar 0]]) BinderInfo.default) BinderInfo.default) BinderInfo.default



#eval show MetaM _ from do
  let o := opAssoc `And
  dbg_trace s!"{o}"
#check assignExprMVar
def smtSimps (mv : MVarId) (assoc : Expr) (null : Expr) (rule : Expr) (arr : Array (Array Expr)) : MetaM Unit := do
  let n := arr.size
  let mut mv' := mv
  for i in [: n] do
    let mut m := arr[i]!.size
    if m > 1 then
      for j in [: m-1] do
        let r ← mv'.rewrite (← mv'.getType) (mkAppN assoc #[arr[i]![m-j-2]!]) true
        mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  let r ← mv'.rewrite (← mv'.getType) rule
  mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  if let some r ← observing? (mv'.rewrite (← mv'.getType) null) then
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  for i in [: n] do
    let mut m := arr[i]!.size
    for j in [: m-1] do
      let some r ← observing? (mv'.rewrite (← mv'.getType) (.app assoc arr[i]![j]!)) | break
      mv' ← mv'.replaceTargetEq r.eNew r.eqProof
  mv'.refl

#check Option

syntax inner := "[" term,* "]"
syntax outer := "[" inner,* "]"
syntax (name := smt_simps) "smt_simps" ident ident ident outer : tactic

def parseInner : TSyntax ``inner → TacticM (Array Expr)
  | `(inner| [$ts,*]) => ts.getElems.mapM (elabTerm · none)
  | _ => throwError "[inner]: wrong usage"

def parseOuter : TSyntax ``outer → TacticM (Array (Array Expr))
  | `(outer| [$is,*]) => is.getElems.mapM parseInner
  | _ => throwError "[outer]: wrong usage"

@[tactic smt_simps] def evalSMTSimps : Tactic := fun stx => do
  let mv : MVarId ← Elab.Tactic.getMainGoal
  let rr ← elabTerm stx[3] none
  let xs ← parseOuter ⟨stx[4]⟩ 
  let op  ← elabTermForApply stx[1]
  let nu  ← elabTermForApply stx[2]
  let r := Expr.const ``and_assoc_eq []
  smtSimps mv op nu rr xs
  Elab.Tactic.replaceMainGoal [mv]

#check getNameOfIdent'
#eval show MetaM _ from do
  let s := Expr.const `And []
  let m := Expr.const (Name.mkStr1 "And") [] 
  IO.println m


#check and_assoc_eq
example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_simps and_assoc_eq and_true bool_and_flatten [[x1, x2], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_simps and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_simps or_assoc_eq or_false bool_or_dup [[x1, x2, x3], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_simps and_assoc_eq and_true bool_and_dup [[x1, x2, x3], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_simps or_assoc_eq or_false bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]


#check Eq.symm (@and_assoc_eq True _ _)
#check and_true

#check mkAppM