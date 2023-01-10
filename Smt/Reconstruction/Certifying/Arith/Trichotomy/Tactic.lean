-- implementation of:
-- https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule16ARITH_TRICHOTOMYE

import Lean

open Lean
open Meta
open Elab.Tactic
open Expr

syntax (name := trichotomy) "trichotomy" term "," term : tactic

@[tactic trichotomy] def evalTrichotomy : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name :=
      match ← getOp t₁, ← getOp t₂ with
      | `LT.lt , `Eq    => `trichotomy₁
      | `Eq    , `LT.lt => `trichotomy₂
      | `LT.lt , `GT.gt => `trichotomy₃
      | `GT.gt , `LT.lt => `trichotomy₄
      | `Eq    , `GT.gt => `trichotomy₅
      | `GT.gt , `Eq    => `trichotomy₆
      | _      , _      => panic! "[trichotomy] invalid operation"
    closeMainGoal (← mkAppM thmName #[h₁, h₂])
where
  getOp : Expr → TacticM Name
    | app _ (app (app (app (app (const nm ..) ..) ..) ..) ..) => pure nm
    | app _ (app (app (app (const nm ..) ..) ..) ..) => pure nm
    | app _ (app (app (const nm ..) ..) ..) => pure nm
    | _ => throwError "[trichotomy] invalid parameter"
