/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean
import Qq
import Smt.Reconstruct.Arith.MultAbsComparison.Lemmas

namespace Smt.Reconstruct.Arith

open Lean Elab Tactic Meta Expr
open Qq

syntax (name := multAbsComparison) "multAbsComparison" ("[" term,* "]")? : tactic

def multAbsComparison₁ (mvar : MVarId) (hs : List Expr) (fname : Name) : MetaM MVarId := do
  let h₁ :: hs' ← pure hs | throwError "unreachable"
  go h₁ hs'
where
  go (acc : Expr) (es : List Expr) : MetaM MVarId :=
    match es with
    | [] => do
      let type ← inferType acc
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type acc
      return mvar'
    | h :: hs => do
      let th ← inferType h
      let thm ← match th with
      | app (app (app (const ``GT.gt ..) _) _) _ => pure ``mult_abs_0
      | app (app (const ``And ..) _) _ => pure ``mult_abs_2
      | _ => throwError "[multAbsComparison]: unexpected hypothesis"
      let acc' ← mkAppM thm #[acc, h]
      go acc' hs

def multAbsComparison₂ (mvar : MVarId) (hs : List Expr) (fname : Name) : MetaM MVarId := do
  let h₁ :: hs' ← pure hs | throwError "unreachable"
  go h₁ hs'
where
  go (acc : Expr) (es : List Expr) : MetaM MVarId :=
    match es with
    | [] => do
      let type ← inferType acc
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type acc
      return mvar'
    | h :: hs => do
      let acc' ← mkAppM ``mult_abs_eq #[acc, h]
      go acc' hs

def parseMultAbsComparison : Syntax → TacticM (List Expr)
  | `(tactic| multAbsComparison [$[$hs],*]) =>
    hs.toList.mapM (fun stx => elabTerm stx.raw none)
  | _ => throwError "[multAbsComparison]: expects a list of premisses"

@[tactic multAbsComparison] def evalMultAbsComparison : Tactic := fun stx => do
  let mvar ← Tactic.getMainGoal
  mvar.withContext do
    let h₁::hs ← parseMultAbsComparison stx | throwError "[multAbsComparison]: empty list of hypothesis"
    let t₁ ← inferType h₁
    let fname ← mkFreshId
    let mvar' ← match t₁ with
    | app (app (app (const ``GT.gt ..) _) _) _ => multAbsComparison₁ mvar (h₁ :: hs) fname
    | app (app (app (const ``Eq ..) _) _) _ => multAbsComparison₂ mvar (h₁ :: hs) fname
    | _ => throwError "[multAbsComparison]: unexpected input - first hypothesis is neither = or >"
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

example (x1 y1 x2 y2 x3 y3 : Int) : abs x1 = abs y1 → abs x2 = abs y2 → abs x3 = abs y3 → abs (x1 * x2 * x3) = abs (y1 * y2 * y3) := by
  intros h1 h2 h3
  multAbsComparison [h1, h2, h3]
