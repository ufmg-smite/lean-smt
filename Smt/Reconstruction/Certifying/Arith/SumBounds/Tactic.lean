/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas
import Smt.Reconstruction.Certifying.Arith.SumBounds.Instances
import Smt.Reconstruction.Certifying.Util

open Lean hiding Rat
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying

def combineBounds (mvar : MVarId) : Expr → Expr → MetaM Expr := fun h₁ h₂ =>
  mvar.withContext do
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name ←
      match ← getOp t₁, ← getOp t₂ with
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
    mkAppM thmName #[h₁, h₂]

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

syntax (name := sumBounds) "sumBounds" "[" term,* "]" : tactic

def parseSumBounds : Syntax → TacticM (List Expr)
  | `(tactic| sumBounds [$[$hs],*]) =>
    hs.toList.mapM (λ stx => elabTerm stx.raw none)
  | _ => throwError "[sumBounds]: expects a list of premisses"

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    let (h, hs) ←
      match ← parseSumBounds stx with
      | h::hs => pure (h, hs)
      | [] => throwError "[sumBounds]: empty list of premisses"
    let mvar ← getMainGoal
    let fname ← mkFreshId
    let mvar' ← sumBoundsMeta mvar h hs fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))


end Smt.Reconstruction.Certifying
