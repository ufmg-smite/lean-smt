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

def parseArithMulAux : Array Term → Term → TacticM (Expr × Expr × Expr × Nat)
  | hs, i => do
    let li: List Expr ←
      hs.toList.mapM (fun h: Term => elabTerm h none)
    let i' ← stxToNat i
    match li with
    | [a, b, c] => return (a, b, c, i')
    | _         => throwError "[arithMul]: List must have 3 elements"

def parseArithMul : Syntax → TacticM (Expr × Expr × Expr × Nat)
  | `(tactic| arithMulPos [ $[$hs],* ], $i) => parseArithMulAux hs i
  | `(tactic| arithMulNeg [ $[$hs],* ], $i) => parseArithMulAux hs i
  | _ => throwError "[arithMul]: wrong usage"

def arithMulMeta (mvar : MVarId) (va vb vc : Expr) (compId : Nat)
  (outName : Name) (thms : List Name) : MetaM MVarId :=
    mvar.withContext do
      let typeC ← inferType vc
      let type ← inferType va
      let vc ←
        match typeC with
        | const `Nat .. =>
          match type with
          | const `Int .. => pure $ mkApp (mkConst ``Int.ofNat) vc
          | const `Rat .. =>
            pure $ mkApp (mkConst ``Rat.ofInt) (mkApp (mkConst ``Int.ofNat) vc)
          | _ => throwError "[arithMul]: unexpected type for first variable"
        | _ => pure vc
      let thmName: Name ←
        if compId <= 4 then
          pure (thms.get! compId) 
        else throwError "[arithMul]: unexpected second argument"
      let inst ←
        match type with
        | const `Int .. => pure $ mkConst ``lorInt
        | const `Rat .. => pure $ mkConst ``lorRat
        | _ => throwError "[arithMul]: unexpected type for first variable"
      let proof := mkApp5 (mkConst thmName) type inst va vb vc
      let proofType ← Meta.inferType proof
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert outName proofType proof
      return mvar'

@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx => do
  trace[smt.profile] m!"[arithMulPos] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let fname ← mkFreshId
  let mvar ← getMainGoal
  let mvar' ← arithMulMeta mvar a b c compId fname
                [ ``arith_mul_pos_lt
                , ``arith_mul_pos_le
                , ``arith_mul_pos_gt
                , ``arith_mul_pos_ge
                , ``arith_mul_pos_eq
                ]
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile] m!"[arithMulPos] end time: {← IO.monoNanosNow}ns"

@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx => do
  trace[smt.profile] m!"[arithMulNeg] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let fname ← mkFreshId
  let mvar ← getMainGoal
  let mvar' ← arithMulMeta mvar a b c compId fname
                [ ``arith_mul_neg_lt
                , ``arith_mul_neg_le
                , ``arith_mul_neg_gt
                , ``arith_mul_neg_ge
                , ``arith_mul_neg_eq
                ]
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile] m!"[arithMulNeg] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying
