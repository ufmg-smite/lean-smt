/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Instances
import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Lemmas
import Smt.Reconstruction.Certifying.Util

import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Vector.Basic

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
    | _ => throwError "[arithMul]: List must have 3 elements"

def parseArithMul : Syntax → TacticM (Expr × Expr × Expr × Nat)
  | `(tactic| arithMulPos [ $[$hs],* ], $i) => parseArithMulAux hs i
  | `(tactic| arithMulNeg [ $[$hs],* ], $i) => parseArithMulAux hs i
  | _ => throwError "[arithMul]: wrong usage"

def operators : Vector Name 5 :=
  ⟨[``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``Eq], rfl⟩  

def castFsts : List Name :=
  [``castFstLT , ``castFstLE , ``castFstGT , ``castFstGE , ``castFstEQ]

def castSnds : List Name :=
  [``castSndLT , ``castSndLE , ``castSndGT , ``castSndGE , ``castSndEQ]

def arithMulMeta (va vb vc : Expr) (pos : Bool) (compId : Nat) (thms : Vector Name 5) :
    MetaM Expr := do
  let mut typeA ← inferType va
  let mut typeB ← inferType vb
  let mut va := va
  let mut vb := vb
  if typeA != typeB then
    if typeA == mkConst ``Int then
      va := mkApp (mkConst ``Rat.ofInt) va
      typeA := mkConst ``Rat
    else
      vb := mkApp (mkConst ``Rat.ofInt) vb
      typeB := mkConst ``Rat
  let typeC ← inferType vc
  let thmName ←
    if lt: compId < 5 then
      pure (thms.get ⟨compId, lt⟩)
    else throwError "[arithMul]: index too large"

  let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
  let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
  let zeroC := if typeC == mkConst ``Int then zeroI else zeroR
  let premiseLeft ←
    if pos then mkAppM ``GT.gt #[vc, zeroC]
    else mkAppM ``LT.lt #[vc, zeroC]

  let operator ←
    if ltPf: compId < 5 then
      pure $ operators.get ⟨compId, ltPf⟩ 
    else throwError "[arithMul]: index too large"
  let premiseRight ← mkAppM operator #[va, vb]

  let premiseType :=
    mkApp2 (mkConst ``And) premiseLeft premiseRight

  match typeA, typeC with
    | const ``Int _, const ``Int _ =>
      mkAppM thmName #[]
    | const ``Int _, const ``Rat _ =>
      withLocalDeclD (← mkFreshId) premiseType $ fun bv => do
        let e₁ ← mkAppM (castSnds.get! compId) #[bv]
        let e₂ ← mkAppM thmName #[e₁]
        mkLambdaFVars #[bv] e₂
    | const ``Rat _, const ``Int _ =>
      withLocalDeclD (← mkFreshId) premiseType $ fun bv => do
        let e₁ ← mkAppM (castFsts.get! compId) #[bv]
        let e₂ ← mkAppM thmName #[e₁]
        mkLambdaFVars #[bv] e₂
    | const ``Rat _, const ``Rat _ =>
      mkAppM thmName #[]
    | _, _ => throwError "[arithMul]: unexpected variable type"

@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx => do
  trace[smt.profile] m!"[arithMulPos] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let mvar ← getMainGoal
  let pf ← arithMulMeta a b c true compId
                ⟨[ ``arith_mul_pos_lt
                 , ``arith_mul_pos_le
                 , ``arith_mul_pos_gt
                 , ``arith_mul_pos_ge
                 , ``arith_mul_pos_eq
                 ], rfl⟩
  let type ← inferType pf
  let fname ← mkFreshId
  let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type pf
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile] m!"[arithMulPos] end time: {← IO.monoNanosNow}ns"

@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx => do
  trace[smt.profile] m!"[arithMulNeg] start time: {← IO.monoNanosNow}ns"
  let (a, b, c, compId) ← parseArithMul stx
  let mvar ← getMainGoal
  let pf ← arithMulMeta a b c false compId
                ⟨[ ``arith_mul_neg_lt
                 , ``arith_mul_neg_le
                 , ``arith_mul_neg_gt
                 , ``arith_mul_neg_ge
                 , ``arith_mul_neg_eq
                 ], rfl⟩
  let type ← inferType pf
  let fname ← mkFreshId
  let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type pf
  replaceMainGoal [mvar']
  evalTactic (← `(tactic| exact $(mkIdent fname)))
  trace[smt.profile] m!"[arithMulNeg] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying
