/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

open Lean Elab Tactic Meta

namespace Smt.Reconstruct.UF

def traceSmtCongr (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def smtCongr (mv : MVarId) (hs : Array Expr) : MetaM Unit := withTraceNode `smt.reconstruct.smtCongr traceSmtCongr do
  mv.withContext do
  let hs ← hs.mapM fun h =>
    return { userName := .anonymous, type := (← Meta.inferType h), value := h }
  let (_, mv) ← mv.assertHypotheses hs
  _ ← mv.congrN

namespace Tactic

syntax (name := smtCongr) "smtCongr"  ("[" term,* "]")? : tactic

def termToSyntax : Term → TacticM Syntax := fun t => pure t

def parseSmtCongr : Syntax → TacticM (Array Expr)
  | `(tactic| smtCongr  [ $[$hs],* ]) => withMainContext do
    let hs' : Array Syntax ← hs.mapM termToSyntax
    hs'.mapM (elabTerm · none)
  | _ => throwError "[smtCongr]: invalid Syntax"

@[tactic smtCongr] def evalSmtCongr : Tactic := fun stx => do
  let es ← parseSmtCongr stx
  UF.smtCongr (← getMainGoal) es

example (a b c d : Int) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

end Smt.Reconstruct.UF.Tactic
