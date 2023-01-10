import Lean

open Lean
open Meta
open Elab.Tactic
open Expr

syntax (name := sumBounds) "sumBounds" term "," term : tactic

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name :=
      match ← getOp t₁, ← getOp t₂ with
      | `LT.lt , `LT.lt => `sumBounds₁
      | `LT.lt , `LT.le => `sumBounds₂
      | `LT.lt , `Eq    => `sumBounds₃
      | `LE.le , `LT.lt => `sumBounds₄
      | `LE.le , `LE.le => `sumBounds₅
      | `LE.le , `Eq    => `sumBounds₆ 
      | `Eq    , `LT.lt => `sumBounds₇
      | `Eq    , `LE.le => `sumBounds₈
      | `Eq    , `Eq    => `sumBounds₉
      | _      , _      => panic! "[sumBounds] invalid operation"
    closeMainGoal (← mkAppM thmName #[h₁, h₂])
where
  getOp : Expr → TacticM Name
    | app (app (app (app (Expr.const nm ..) ..) ..) ..) .. => pure nm
    | app (app (app (Expr.const nm ..) ..) ..) .. => pure nm
    | _ => throwError "[sumBounds] invalid parameter"
