import Lean

import Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas
import Smt.Reconstruction.Certifying.Arith.SumBounds.Instances

open Lean hiding Rat
open Meta Elab.Tactic Expr

def combineBounds : Expr → Expr → TacticM Expr := fun h₁ h₂ =>
  withMainContext do
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name :=
      match ← getOp t₁, ← getOp t₂ with
      | `LT.lt , `LT.lt => `sumBounds₁
      | `LT.lt , `LE.le => `sumBounds₂
      | `LT.lt , `Eq    => `sumBounds₃
      | `LE.le , `LT.lt => `sumBounds₄
      | `LE.le , `LE.le => `sumBounds₅
      | `LE.le , `Eq    => `sumBounds₆ 
      | `Eq    , `LT.lt => `sumBounds₇
      | `Eq    , `LE.le => `sumBounds₈
      | `Eq    , `Eq    => `sumBounds₉
      | _      , _      => panic! "[sumBounds] invalid operation"
    mkAppM thmName #[h₁, h₂]
where
  getOp : Expr → TacticM Name
    | app (app (app (app (Expr.const nm ..) ..) ..) ..) .. => pure nm
    | app (app (app (Expr.const nm ..) ..) ..) .. => pure nm
    | _ => throwError "[sumBounds] invalid parameter"

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
    go h hs
where
  go : Expr → List Expr → TacticM Unit
    | acc, []    => closeMainGoal acc
    | acc, e::es => do
      let acc' ← combineBounds acc e
      go acc' es

example {a b c d e f : Nat} : a < d → b < e → c < f → a + b + c < d + e + f := by
  intros h₁ h₂ h₃
  sumBounds [h₁, h₂, h₃]

example {a b c d e f w z : Int} :
  a ≤ d → b ≤ e → c ≤ f → w ≤ z → a + b + c + w ≤ d + e + f + z := by
    intros h₁ h₂ h₃ h₄
    sumBounds [h₁, h₂, h₃, h₄]

example {a b c d e f : ℚ} : a < d → b ≤ e → c ≤ f → a + b + c < d + e + f := by
  intros h₁ h₂ h₃
  sumBounds [h₁, h₂, h₃]
