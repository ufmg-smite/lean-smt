/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Lean

import Smt.Reconstruct.Prop.Rewrites

theorem Eq.trans₂ {α} {a b c d : α} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = d :=
  h₁ ▸ h₂ ▸ h₃

namespace Smt.Reconstruct.Tactic

open Lean Elab.Tactic
open Smt.Reconstruct.Prop

def traceSmtRw (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def smtRw (mv : MVarId) (op : Expr) (id : Expr) (rr : Expr) (xss : Array (Array Expr)) : MetaM Unit :=
  withTraceNode `smt.reconstruct.DSL_REWRITE.tac traceSmtRw do
  let xs := xss.map (fun xs => xs[1:].foldr (mkApp2 op) (xs[0]?.getD id))
  let some (α, l, r) := (← mv.getType).eq?
    | throwError "[smt_rw] expected a top level equality with AC operator on lhs and/or rhs, got {← mv.getType}"
  let h₂ := mkAppN rr xs
  let some (_, ml, mr) := (← Meta.inferType h₂).eq?
    | throwError "[smt_rw] error applying rewrite rule to arguments: {mkAppN rr xs}"
  let lvl ← Meta.getLevel α
  let h₁ ← Meta.mkFreshExprMVar (mkApp3 (.const ``Eq [lvl]) α l ml)
  let h₃ ← Meta.mkFreshExprMVar (mkApp3 (.const ``Eq [lvl]) α mr r)
  Meta.AC.rewriteUnnormalizedRefl h₁.mvarId!
  Meta.AC.rewriteUnnormalizedRefl h₃.mvarId!
  mv.assign (mkApp8 (.const ``Eq.trans₂ [lvl]) α l ml mr r h₁ h₂ h₃)

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
  let op ← elabTermForApply stx[1]
  let id ← elabTermForApply stx[2]
  let rr ← elabTermForApply stx[3]
  let xs ← parseOuter ⟨stx[4]⟩
  let mv : MVarId ← getMainGoal
  smtRw mv op id rr xs

example : (x1 ∧ x2 ∧ x3 ∧ (b ∧ y1 ∧ y2 ∧ True) ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And True bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ b ∧ z1 ∧ z2 ∧ True) = (x1 ∧ x2 ∧ x3 ∧ b ∧ y1 ∧ y2 ∧ z1 ∧ z2 ∧ True) := by
  smt_rw And True bool_and_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ b ∨ z1 ∨ z2 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ y2 ∨ z1 ∨ z2 ∨ False) := by
  smt_rw Or False bool_or_flatten [[x1, x2, x3], [b], [y1, y2], [z1, z2]]

example : (x1 ∨ x2 ∨ x3 ∨ (b ∨  y1 ∨ False) ∨ z1 ∨ False) = (x1 ∨ x2 ∨ x3 ∨ b ∨ y1 ∨ z1 ∨ False) := by
  smt_rw Or False bool_or_flatten [[x1, x2, x3], [b], [y1], [z1]]

example : (p ∨ ¬p) = True := by
  smt_rw Or False bool_or_taut [[], [p], [], []]

end Smt.Reconstruct.Tactic
