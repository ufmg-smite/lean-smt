import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Lemmas

import Mathlib.Data.Rat.Order
import Mathlib.Data.Int.Order.Basic

import Lean

open Lean hiding Rat
open Elab.Tactic Expr Meta

syntax (name := arithMulPos) "arithMulPos" term "," term : tactic
@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← Meta.inferType h₁
    let thmName := getThmName t₁
    let proof : Expr ← mkAppM thmName #[h₁, h₂]
    closeMainGoal proof
where getThmName : Expr → Name
        | app (app (app (app (app (const nm ..) ..) ..) ..) ..) _ => matchNameThm nm
        | app (app (app (app (const nm ..) ..) ..) ..) _ => matchNameThm nm
        | _ => panic! "[arithMulPos]: structure not supported"
      matchNameThm : Name → Name
        | `LE.le => `arith_mul_pos_le
        | `LT.lt => `arith_mul_pos_lt
        | `GT.gt => `arith_mul_pos_gt
        | `GE.ge => `arith_mul_pos_ge
        | _ => panic! "[arithMulPos]: invalid comparator"

syntax (name := arithMulNeg) "arithMulNeg" term "," term : tactic
@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← Meta.inferType h₁
    let thmName := getThmName t₁
    let proof : Expr ← mkAppM thmName #[h₁, h₂]
    closeMainGoal proof
where getThmName : Expr → Name
        | app (app (app (app (app (const nm ..) ..) ..) ..) ..) _ => matchNameThm nm
        | app (app (app (app (const nm ..) ..) ..) ..) _ => matchNameThm nm
        | _ => panic! "[arithMulNeg]: structure not supported"
      matchNameThm : Name → Name
        | `LE.le => `arith_mul_neg_le
        | `LT.lt => `arith_mul_neg_lt
        | `GT.gt => `arith_mul_neg_gt
        | `GE.ge => `arith_mul_neg_ge
        | _ => panic! "[arithMulNeg]: invalid comparator"

example {a b c : Int} : a < b → 0 < c → c * a < c * b := by
  intros h₁ h₂
  arithMulPos h₁, h₂

example {a b c : ℚ} : a ≤ b → 0 > c → c * a ≥ c * b := by
  intros h₁ h₂
  arithMulNeg h₁, h₂
