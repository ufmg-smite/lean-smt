import Lean

import Mathlib.Data.Nat.Parity

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Arith.ArithMulSign.Lemmas

open Lean Elab Tactic Meta Expr
open Smt.Reconstruction.Certifying

abbrev MulSignInput := List (Name × Bool × Nat)

--              var names/neg or pos/ exponents
-- arithMulSign [a, b, c] [1, -1, 1], [2, 3, 1]
syntax (name := arithMulSign) "arithMulSign" ("[" term,* "]")? "," ("[" term,* "]") "," ("[" term,* "]")? : tactic

def parseArithMulSign : Syntax → TacticM MulSignInput
  | `(tactic| arithMulSign [ $[$ns],* ], [ $[$bs],* ], [ $[$es],* ]) => do
    let names: List Name :=
      ns.toList.map (fun h: Term =>
                      let hIdent: Ident := ⟨h⟩
                      hIdent.getId
                    )
    let bools: List Bool ←
      bs.toList.mapM (fun h: Term => do
                      let hExpr ← elabTerm h none
                      let o := getNatLit? hExpr
                      pure $ Option.isSome o
                    )
    let exps : List Nat ← es.toList.mapM stxToNat
    pure (names.zip (bools.zip exps))
  | _ => throwError "[ArithMulSign]: wrong syntax"

@[tactic arithMulSign] def evalArithMulSign : Tactic := fun stx =>
  withMainContext do
    let data ← parseArithMulSign stx
    let mvar ← getMainGoal
    mvar.withContext do
      let answer ← go true data data (mkConst `tmp)
      return ()
      /- replaceMainGoal [mvar'] -/
where
-- acc is a partial proof corresponding to the sign of the prefix of the multiplication
  go (first : Bool) (xs xs' : MulSignInput) (acc : Expr) : MetaM Expr :=
    match xs with
    | [] =>
      sorry
    | (name, pol, exp) :: t => do
      let lctx ← getLCtx
      let val := (lctx.findFromUserName? name).get!.toExpr
      let type: Expr ←
        if pol then
          mkAppM ``GT.gt #[val, mkNatLit 0]
        else mkAppM ``LT.lt #[val, mkNatLit 0]
      withLocalDeclD (← mkFreshId) type $ fun bv => do
        let curr ←
          if pol then pure bv
          else
            let rflExpr := mkApp2 (mkConst ``rfl) (mkConst ``Nat) (mkNatLit exp)
            if decide (Even exp) then
              let evenExp ← mkAppM `Nat.even_iff.mpr #[rflExpr]
              mkAppM ``powEven #[bv, evenExp]
            else
              let oddExp ← mkAppM `Nat.odd_iff.mpr #[rflExpr]
              mkAppM ``powOdd #[bv, oddExp]
        let acc' ←
          if first then pure curr
          else
            let type ← inferType acc
            let valPos := (← getOp type) == `GT.gt
            if pol then
              if valPos then
                sorry
              else sorry
            else
              if valPos then
                sorry
              else sorry
        let rc ← go false t xs' acc'
        mkLambdaFVars #[bv] rc

