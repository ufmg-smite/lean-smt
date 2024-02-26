/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruct.Arith.MulPosNeg.Lemmas
import Smt.Reconstruct.Arith.SumBounds.Lemmas
import Smt.Reconstruct.Arith.SumBounds.Instances
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Arith

open Lean
open Meta Elab.Tactic Expr

theorem castEQ : ∀ {a b : Int}, a = b → Real.intCast.intCast a = Real.intCast.intCast b := by
  intros a b h
  rw [h]

def getCastRelThm (rel : Name) : Name :=
  match rel with
  | ``LT.lt => ``castLT
  | ``LE.le => ``castLE
  | ``Eq    => ``castEQ
  | _ => `unreachable

def combineBounds (mvar : MVarId) : Expr → Expr → MetaM Expr := fun h₁ h₂ =>
  mvar.withContext do
    let t₁ ← inferType h₁
    let rel₁ ← getOp t₁
    let t₂ ← inferType h₂
    let rel₂ ← getOp t₂
    let tp₁ ← getOpType t₁
    let tp₂ ← getOpType t₂
    let (h₁, h₂) ←
      match tp₁, tp₂ with
      | const `Int .., const `Real .. =>
        let thm := getCastRelThm rel₁
        pure (← mkAppM thm #[h₁], h₂)
      | const `Real .., const `Int .. =>
        let thm := getCastRelThm rel₂
        pure (h₁, ← mkAppM thm #[h₂])
      | _, _ => pure (h₁, h₂)
    let thmName : Name ←
      match rel₂, rel₁ with
      | ``LT.lt , ``LT.lt => pure ``sumBounds₁
      | ``LT.lt , ``LE.le => pure ``sumBounds₂
      | ``LT.lt , ``Eq    => pure ``sumBounds₃
      | ``LE.le , ``LT.lt => pure ``sumBounds₄
      | ``LE.le , ``LE.le => pure ``sumBounds₅
      | ``LE.le , ``Eq    => pure ``sumBounds₆
      | ``Eq    , ``LT.lt => pure ``sumBounds₇
      | ``Eq    , ``LE.le => pure ``sumBounds₈
      | ``Eq    , ``Eq    => pure ``sumBounds₉
      | _      , _      => throwError "[sumBounds] invalid operation"
    mkAppM thmName #[h₂, h₁]
where
  getOpType : Expr → MetaM Expr
  | app (Expr.const ``Not ..) e' => getOpType e'
  | app (app (app (app (app (Expr.const _ ..) tp) ..) ..) ..) .. => pure tp
  | app (app (app (app (Expr.const _ ..) tp) ..) ..) .. => pure tp
  | app (app (app (Expr.const _ ..) tp) ..) .. => pure tp
  | _ => throwError "[getOp] invalid parameter"

def sumBounds (mv : MVarId) (hs : Array Expr) : MetaM Unit := mv.withContext do
  if hs.isEmpty then
    throwError "[sumBounds]: empty list of premisses"
  let mut acc := hs[0]!
  for i in [1:hs.size] do
    acc ← combineBounds mv acc hs[i]!
  mv.assignIfDefeq acc

def sumBoundsMeta (mvar : MVarId) (h : Expr) (hs : List Expr) (name : Name)
    : MetaM MVarId :=
  mvar.withContext do
    go h hs
where
  go : Expr → List Expr → MetaM MVarId
    | acc, [] => do
      let type ← inferType acc
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type acc
      return mvar'
    | acc, h::hs => do
      let acc ← combineBounds mvar acc h
      go acc hs

namespace Tactic

syntax (name := sumBounds) "sumBounds" "[" term,* "]" : tactic

def parseSumBounds : Syntax → TacticM (List Expr)
  | `(tactic| sumBounds [$[$hs],*]) =>
    hs.toList.mapM (fun stx => elabTerm stx.raw none)
  | _ => throwError "[sumBounds]: expects a list of premisses"

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[sumBounds] start time: {← IO.monoNanosNow}ns"
    let (h, hs) ←
      match ← parseSumBounds stx with
      | h::hs =>
        let h'::hs' := List.reverse (h::hs) | throwError "unreachable"
        pure (h', hs')
      | [] => throwError "[sumBounds]: empty list of premisses"
    let mvar ← getMainGoal
    let fname ← mkFreshId
    let mvar' ← sumBoundsMeta mvar h hs fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[sumBounds] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruct.Arith.Tactic
