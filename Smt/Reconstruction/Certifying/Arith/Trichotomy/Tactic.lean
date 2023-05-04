/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

-- we must import those to have visible instances of LinearOrder of
-- Nat, Int and Rat
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Rat.Order

import Smt.Reconstruction.Certifying.Arith.Trichotomy.Lemmas

open Lean hiding Rat
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying

syntax (name := trichotomy) "trichotomy" term "," term : tactic

@[tactic trichotomy] def evalTrichotomy : Tactic := fun stx =>
  withMainContext do
    let h₁ ← notLeToLt (← elabTerm stx[1] none)
    let h₂ ← notLeToLt (← elabTerm stx[3] none)
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
    closeMainGoal (← mkAppM thmName #[h₁, h₂])
where
  getOp : Expr → TacticM Name
    | app _ (app (app (app (app (const nm ..) ..) ..) ..) ..) => pure nm
    | app _ (app (app (app (const nm ..) ..) ..) ..) => pure nm
    | _ => throwError "[trichotomy] invalid parameter"
  notLeToLt : Expr → TacticM Expr := λ e => do
    match ← inferType e with
      | app (app (app (app (app (const ``LE.le ..) ..) ..) ..) ..) _ => mkAppM ``not_gt_of_le #[e]
      | app (app (app (app (const ``LE.le ..) ..) ..) ..) _ => mkAppM ``not_gt_of_le #[e]
      | app (app (app (app (app (const ``GE.ge ..) ..) ..) ..) ..) _ => mkAppM ``not_lt_of_ge #[e]
      | app (app (app (app (const ``GE.ge ..) ..) ..) ..) _ => mkAppM ``not_lt_of_ge #[e]
      | _ => pure e

end Smt.Reconstruction.Certifying
