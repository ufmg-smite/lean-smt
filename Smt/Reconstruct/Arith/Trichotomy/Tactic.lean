/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

-- we must import those to have visible instances of LinearOrder of
-- Nat, Int and Rat
import Mathlib.Data.Rat.Order
import Mathlib.Init.Data.Int.Order
import Mathlib.Init.Data.Nat.Lemmas

import Smt.Reconstruct.Arith.Trichotomy.Lemmas

namespace Smt.Reconstruct.Arith

open Lean hiding Rat
open Meta Elab.Tactic Expr

def trichotomyMeta (mvar : MVarId) (h₁ h₂ : Expr) (name : Name) : MetaM MVarId :=
  mvar.withContext do
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name ←
      match ← getOp t₁, ← getOp t₂ with
      | ``LT.lt , ``Eq    => pure ``trichotomy₁
      | ``Eq    , ``LT.lt => pure ``trichotomy₂
      | ``LT.lt , ``GT.gt => pure ``trichotomy₃
      | ``GT.gt , ``LT.lt => pure ``trichotomy₄
      | ``Eq    , ``GT.gt => pure ``trichotomy₅
      | ``GT.gt , ``Eq    => pure ``trichotomy₆
      | _      , _      => throwError "[trichotomy] invalid operation"
    let answer ← mkAppM thmName #[h₁, h₂]
    let answerType ← inferType answer
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name answerType answer
    return mvar'

syntax (name := trichotomy) "trichotomy" term "," term : tactic

@[tactic trichotomy] def evalTrichotomy : Tactic := fun stx =>
  withMainContext do
    trace[smt.profile.reconstruct] m!"[trichotomy] start time: {← IO.monoNanosNow}ns"
    let h₁ ← notLeToLt (← elabTerm stx[1] none)
    let h₂ ← notLeToLt (← elabTerm stx[3] none)
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← trichotomyMeta mvar h₁ h₂ fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[trichotomy] end time: {← IO.monoNanosNow}ns"
where
  notLeToLt : Expr → MetaM Expr := λ e => do
    match ← inferType e with
      | app (app (app (app (app (const ``LE.le ..) ..) ..) ..) ..) _ => mkAppM ``not_gt_of_le #[e]
      | app (app (app (app (const ``LE.le ..) ..) ..) ..) _ => mkAppM ``not_gt_of_le #[e]
      | app (app (app (app (app (const ``GE.ge ..) ..) ..) ..) ..) _ => mkAppM ``not_lt_of_ge #[e]
      | app (app (app (app (const ``GE.ge ..) ..) ..) ..) _ => mkAppM ``not_lt_of_ge #[e]
      | _ => pure e

end Smt.Reconstruct.Arith
