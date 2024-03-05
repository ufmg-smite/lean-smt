/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Mathlib.Data.Real.Basic

import Smt.Reconstruct.Arith.MulPosNeg.Lemmas
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Arith

open Lean
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
    | _ => throwError "[arithMul]: List must have 3 elements"

def parseArithMul : Syntax → TacticM (Expr × Expr × Expr × Nat)
  | `(tactic| arithMulPos [ $[$hs],* ], $i) => parseArithMulAux hs i
  | `(tactic| arithMulNeg [ $[$hs],* ], $i) => parseArithMulAux hs i
  | _ => throwError "[arithMul]: wrong usage"

def operators : List Name :=
  [``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``Eq]

def castFsts : List Name :=
  [``castFstLT , ``castFstLE , ``castFstGT , ``castFstGE , ``castFstEQ]

def castSnds : List Name :=
  [``castSndLT , ``castSndLE , ``castSndGT , ``castSndGE , ``castSndEQ]

def arithMulMeta (va vb vc : Expr) (pos : Bool) (compId : Nat) (thms : List Name) :
    MetaM Expr := do
  let mut typeA ← inferType va
  let mut typeB ← inferType vb
  let mut va := va
  let mut vb := vb
  if typeA != typeB then
    if typeA == mkConst ``Int then
      va := mkApp (mkConst ``zToR) va
      typeA := mkConst ``Real
    else
      vb := mkApp (mkConst ``zToR) vb
      typeB := mkConst ``Real
  let typeC ← inferType vc
  let thmName ←
    if compId < 5 then
      pure (thms.get! compId)
    else throwError "[arithMul]: index too large"

  let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
  let zeroR ← mkAppOptM' (.const ``OfNat.ofNat [.zero]) #[mkConst ``Real, (mkNatLit 0), none]
  let zeroC := if typeC == mkConst ``Int then zeroI else zeroR
  let premiseLeft ←
    if pos then mkAppM ``LT.lt #[zeroC, vc]
    else mkAppM ``LT.lt #[vc, zeroC]
  let operator ←
    if compId < 5 then
      pure $ operators.get! compId
    else throwError "[arithMul]: index too large"
  let premiseRight ← mkAppM operator #[va, vb]

  let premiseType :=
    mkApp2 (mkConst ``And) premiseLeft premiseRight

  match typeA, typeC with
    | const ``Int _, const ``Int _ =>
      mkAppM thmName #[]
    | const ``Int _, const ``Real _ =>
      withLocalDeclD (← mkFreshId) premiseType $ fun bv => do
        let e₁ ← mkAppM (castSnds.get! compId) #[bv]
        let e₂ ← mkAppM thmName #[e₁]
        mkLambdaFVars #[bv] e₂
    | const ``Real _, const ``Int _ =>
      withLocalDeclD (← mkFreshId) premiseType $ fun bv => do
        let e₁ ← mkAppM (castFsts.get! compId) #[bv]
        let e₂ ← mkAppM thmName #[e₁]
        mkLambdaFVars #[bv] e₂
    | const ``Real _, const ``Real _ =>
      mkAppM thmName #[]
    | _, _ => throwError "[arithMul]: unexpected variable type"

@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx => do
  trace[smt.profile.reconstruct] m!"[arithMulPos] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let mvar ← getMainGoal
  let pf ← arithMulMeta a b c true compId
                [ ``arith_mul_pos_lt
                , ``arith_mul_pos_le
                , ``arith_mul_pos_gt
                , ``arith_mul_pos_ge
                , ``arith_mul_pos_eq
                ]
  let type ← inferType pf
  let fname ← mkFreshId
  let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type pf
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile.reconstruct] m!"[arithMulPos] end time: {← IO.monoNanosNow}ns"

@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx => do
  trace[smt.profile.reconstruct] m!"[arithMulNeg] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let mvar ← getMainGoal
  let pf ← arithMulMeta a b c false compId
                [ ``arith_mul_neg_lt
                , ``arith_mul_neg_le
                , ``arith_mul_neg_gt
                , ``arith_mul_neg_ge
                , ``arith_mul_neg_eq
                ]
  let type ← inferType pf
  let fname ← mkFreshId
  let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type pf
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile.reconstruct] m!"[arithMulNeg] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruct.Arith
