import Lean

open Lean Elab.Tactic Expr Meta

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

