/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Real.Basic

import Smt.Reconstruct.Arith.ArithMulSign.Lemmas
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Arith

open Lean Elab Tactic Meta Expr

inductive Pol where
 | Neg : Pol -- 0
 | NZ  : Pol -- 1
 | Pos : Pol -- 2
 deriving BEq

def intLOR := mkApp2 (.const ``LinearOrderedCommRing.toLinearOrderedRing [.zero])
                     (.const ``Int []) (.const ``Int.instLinearOrderedCommRing [])

def RealLOR := Expr.const ``Real.instLinearOrderedRing []


def traceMulSign (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def mulSign (mv : MVarId) (xs : Array (Expr × Fin 3 × Nat)) : MetaM Unit := withTraceNode `smt.reconstruct.mulSign traceMulSign do
  mv.assign (← go true xs.toList (mkConst `empty) (mkConst `empty))
where
  go (first : Bool) (xs : (List (Expr × Fin 3 × Nat))) (prodSignPf : Expr) (prod : Expr) : MetaM Expr :=
  match xs with
  | [] => return prodSignPf
  | (expr, pol, exp) :: t => do
    let exprType ← inferType expr
    let exprIsInt ←
      match exprType with
      | .const `Rat .. => pure false
      | .const `Int .. => pure true
      | _ => throwError "[arithMulSign]: unexpected type for expression"
    let lorInst := if exprIsInt then intLOR else RealLOR
    let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
    let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
    -- zero with the same type as the current argument
    let currZero := if exprIsInt then zeroI else zeroR
    let bindedType: Expr ← match pol with
      | 0 => mkAppM ``LT.lt #[expr, currZero]
      | 1 => mkAppM ``Ne    #[expr, currZero]
      | 2 => mkAppM ``GT.gt #[expr, currZero]
    let expParityPf ← do
      if exp % 2 == 0 then
        let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 0)]
        let iffExp := mkApp (mkConst ``Nat.even_iff) (mkNatLit exp)
        mkAppM ``Iff.mpr #[iffExp, rflExpr]
      else
        let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 1)]
        let iffExp := mkApp (mkConst ``Nat.odd_iff) (mkNatLit exp)
        mkAppM ``Iff.mpr #[iffExp, rflExpr]
    withLocalDeclD (← mkFreshId) bindedType $ fun bv => do
      let exprPowSignPf ←
        if exp == 1 then
          pure bv
        else
          match pol with
          | 1 =>
            pure $ mkApp6 (mkConst ``nonZeroEvenPow) exprType lorInst (mkNatLit exp) expr bv expParityPf
          | 2 =>
            pure $ mkApp5 (mkConst ``powPos) exprType lorInst (mkNatLit exp) expr bv
          | 0 =>
            if exp % 2 == 0 then
              mkAppM ``powNegEven #[bv, expParityPf]
            else
              mkAppM ``powNegOdd #[bv, expParityPf]
      let exprPow ←
        if exp == 1 then
          pure expr
        else mkAppM ``Pow.pow #[expr, mkNatLit exp]
      let prodType ←
        if first then
          pure exprType
        else inferType prod
      let prodIsInt ←
        match prodType with
        | .const `Int .. => pure true
        | .const `Rat .. => pure false
        | _ => throwError "[arithMulSign]: unexpected type for accumulated product"
      let prodSignPfType ←
        if first then
          inferType exprPowSignPf
        else inferType prodSignPf
      let prodPos := (← getOp prodSignPfType) == `GT.gt
      -- normalize types in case one is rat and the other is int
      let (exprPow', prod', exprPowSignPf', prodSignPf') :=
        match exprIsInt, prodIsInt with
        | false, true  =>
          let prodSignPf' :=
            if prodPos then
              mkApp2 (mkConst ``castPos) prod prodSignPf
            else mkApp2 (mkConst ``castNeg) prod prodSignPf
          (exprPow, mkApp (mkConst ``Rat.ofInt) prod, exprPowSignPf, prodSignPf')
        | true, false  =>
          let exprPowSignPf' :=
            if pol == 2 || pol == 1 || exp % 2 == 0 then
              mkApp2 (mkConst ``castPos) exprPow exprPowSignPf
            else mkApp2 (mkConst ``castNeg) exprPow exprPowSignPf
          (mkApp (mkConst ``Rat.ofInt) exprPow, prod, exprPowSignPf', prodSignPf)
        | _, _   => (exprPow, prod, exprPowSignPf, prodSignPf)
      let answer ←
        if first then pure exprPowSignPf
        else
          if pol == 2 || pol == 1 || exp % 2 == 0 then
            if prodPos then
              mkAppOptM ``combineSigns₁ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
            else mkAppOptM ``combineSigns₂ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
          else
            if prodPos then
              mkAppOptM ``combineSigns₃ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
            else mkAppOptM ``combineSigns₄ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
      let prod' ←
        if first then
          pure exprPow
        else mkAppM ``Mul.mul #[prod', exprPow']
      let rc ← go false t answer prod'
      mkLambdaFVars #[bv] rc

namespace Tactic

--              var names/neg or pos/ exponents
-- arithMulSign [a, b, c] [1, -1, 1], [2, 3, 1]
syntax (name := arithMulSign) "arithMulSign" ("[" term,* "]")? "," ("[" term,* "]") "," ("[" term,* "]")? : tactic

def parseArithMulSign : Syntax → TacticM (List (Expr × Pol × Nat))
  | `(tactic| arithMulSign [ $[$ns],* ], [ $[$bs],* ], [ $[$es],* ]) => do
    let exprs: List Expr ←
      ns.toList.mapM (fun h: Term => elabTerm h none)
    let bools: List Pol ←
      bs.toList.mapM (fun h: Term => do
                      let hExpr ← elabTerm h none
                      match getNatLit? hExpr with
                      | none   => pure Pol.Neg
                      | some 0 => pure Pol.NZ
                      | some 1 => pure Pol.Pos
                      | _      => throwError "[arithMulSign]: invalid polarity"
                    )
    let exps : List Nat ← es.toList.mapM stxToNat
    pure (exprs.zip (bools.zip exps))
  | _ => throwError "[ArithMulSign]: wrong syntax"

@[tactic arithMulSign] def evalArithMulSign : Tactic := fun stx => do
  let mvar ← getMainGoal
  mvar.withContext do
    trace[smt.profile.reconstruct] m!"[arithMulSign] start time: {← IO.monoNanosNow}ns"
    let data ← parseArithMulSign stx
    let answer ← go true data (mkConst `empty) (mkConst `empty)
    let answerType ← inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname answerType answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[arithMulSign] end time: {← IO.monoNanosNow}ns"
where
-- acc is a partial proof corresponding to the sign of the prefix of the multiplication
  go (first : Bool) (xs : (List (Expr × Pol × Nat))) (prodSignPf : Expr) (prod : Expr) : MetaM Expr :=
    match xs with
    | [] => return prodSignPf
    | (expr, pol, exp) :: t => do
      let exprType ← inferType expr
      let exprIsInt ←
        match exprType with
        | .const `Real .. => pure false
        | .const `Int .. => pure true
        | _ => throwError "[arithMulSign]: unexpected type for expression"
      let lorInst := if exprIsInt then intLOR else RealLOR
      let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
      let zeroR ← mkAppOptM' (.const ``OfNat.ofNat [.zero]) #[mkConst ``Real, (mkNatLit 0), none]
      -- zero with the same type as the current argument
      let currZero := if exprIsInt then zeroI else zeroR
      let bindedType: Expr ←
        match pol with
        | Pol.Neg => mkAppM ``LT.lt #[expr, currZero]
        | Pol.NZ  => mkAppM ``Ne    #[expr, currZero]
        | Pol.Pos => mkAppM ``GT.gt #[expr, currZero]
      let expParityPf ← do
        if exp % 2 == 0 then
          let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 0)]
          let iffExp := mkApp (mkConst ``Nat.even_iff) (mkNatLit exp)
          mkAppM ``Iff.mpr #[iffExp, rflExpr]
        else
          let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 1)]
          let iffExp := mkApp (mkConst ``Nat.odd_iff) (mkNatLit exp)
          mkAppM ``Iff.mpr #[iffExp, rflExpr]
      withLocalDeclD (← mkFreshId) bindedType $ fun bv => do
        let exprPowSignPf ←
          if exp == 1 then
            pure bv
          else
            match pol with
            | Pol.NZ =>
              pure $ mkApp6 (mkConst ``nonZeroEvenPow) exprType lorInst (mkNatLit exp) expr bv expParityPf
            | Pol.Pos =>
              pure $ mkApp5 (mkConst ``powPos) exprType lorInst (mkNatLit exp) expr bv
            | Pol.Neg =>
              if exp % 2 == 0 then
                mkAppM ``powNegEven #[bv, expParityPf]
              else
                mkAppM ``powNegOdd #[bv, expParityPf]
        let exprPow ←
          if exp == 1 then
            pure expr
          else mkAppM ``Pow.pow #[expr, mkNatLit exp]
        let prodType ←
          if first then
            pure exprType
          else inferType prod
        let prodIsInt ←
          match prodType with
          | .const `Int .. => pure true
          | .const `Real .. => pure false
          | _ => throwError "[arithMulSign]: unexpected type for accumulated product"
        let prodSignPfType ←
          if first then
            inferType exprPowSignPf
          else inferType prodSignPf
        let prodPos := (← getOp prodSignPfType) == `GT.gt
        -- normalize types in case one is real and the other is int
        let (exprPow', prod', exprPowSignPf', prodSignPf') :=
          match exprIsInt, prodIsInt with
          | false, true  =>
            let prodSignPf' :=
              if prodPos then
                mkApp2 (mkConst ``castPos) prod prodSignPf
              else mkApp2 (mkConst ``castNeg) prod prodSignPf
            (exprPow, mkApp (mkConst ``zToR) prod, exprPowSignPf, prodSignPf')
          | true, false  =>
            let exprPowSignPf' :=
              if pol == Pol.Pos || pol == Pol.NZ || exp % 2 == 0 then
                mkApp2 (mkConst ``castPos) exprPow exprPowSignPf
              else mkApp2 (mkConst ``castNeg) exprPow exprPowSignPf
            (mkApp (mkConst ``zToR) exprPow, prod, exprPowSignPf', prodSignPf)
          | _, _   => (exprPow, prod, exprPowSignPf, prodSignPf)
        let answer ←
          if first then pure exprPowSignPf
          else
            if pol == Pol.Pos || pol == Pol.NZ || exp % 2 == 0 then
              if prodPos then
                mkAppOptM ``combineSigns₁ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
              else mkAppOptM ``combineSigns₂ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
            else
              if prodPos then
                mkAppOptM ``combineSigns₃ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
              else mkAppOptM ``combineSigns₄ #[none, none, exprPow', prod', exprPowSignPf', prodSignPf']
        let prod' ←
          if first then
            pure exprPow
          else mkAppM ``Mul.mul #[prod', exprPow']
        let rc ← go false t answer prod'
        mkLambdaFVars #[bv] rc

end Smt.Reconstruct.Arith.Tactic
