/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Instances
import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Lemmas
import Smt.Reconstruction.Certifying.Util

import Mathlib.Data.Rat.Order
import Mathlib.Data.Int.Order.Basic

import Lean

namespace Smt.Reconstruction.Certifying

open Lean hiding Rat
open Elab Tactic Expr Meta

syntax (name := arithMulPos) "arithMulPos" ("[" term,* "]")? "," term : tactic
syntax (name := arithMulNeg) "arithMulNeg" ("[" term,* "]")? "," term : tactic

def parseArithMulAux : Array Term → Term → TacticM (List Name × Nat)
  | hs, i => do
    let li: List Name :=
      hs.toList.map (fun h: Term =>
                       let hIdent : Ident := ⟨h⟩
                       hIdent.getId
                    )
    let i' ← stxToNat i
    return (li, i')

def parseArithMul : Syntax → TacticM (List Name × Nat)
  | `(tactic| arithMulPos [ $[$hs],* ], $i) => parseArithMulAux hs i
  | `(tactic| arithMulNeg [ $[$hs],* ], $i) => parseArithMulAux hs i
  | _ => throwError "[arithMul]: wrong usage"

def evalArithMulAux : Syntax → List Name → TacticM Unit:=
  fun stx thms =>
    withMainContext do
      let (names, compId) ← parseArithMul stx
      let (a, b, c) ←
        match names with
        | [a', b', c'] => pure (a', b', c')
        | _            => throwError "[arithMulNeg]: List must have 3 elements"
      let lctx ← getLCtx
      let va := (lctx.findFromUserName? a).get!.toExpr
      let vb := (lctx.findFromUserName? b).get!.toExpr
      let vc := (lctx.findFromUserName? c).get!.toExpr
      let type ← inferType va
      let thmName: Name ←
        if compId <= 3 then
          pure (thms.get! compId) 
        else throwError "[arithMul]: unexpected second argument"
      let inst ←
        match type with
        | const `Int .. => pure $ mkConst ``lorInt
        | const `Rat .. => pure $ mkConst ``lorRat
        | _ => throwError "[arithMulNeg]: unexpected type for variable"
      let proof := mkApp5 (mkConst thmName) type inst va vb vc
      closeMainGoal proof

@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx =>
  evalArithMulAux stx [ ``arith_mul_pos_lt
                      , ``arith_mul_pos_le
                      , ``arith_mul_pos_gt
                      , ``arith_mul_pos_ge
                      ]

@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx =>
  evalArithMulAux stx [ ``arith_mul_neg_lt
                      , ``arith_mul_neg_le
                      , ``arith_mul_neg_gt
                      , ``arith_mul_neg_ge
                      ]

end Smt.Reconstruction.Certifying
