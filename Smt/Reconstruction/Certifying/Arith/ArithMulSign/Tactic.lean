import Lean

import Mathlib.Data.Nat.Parity

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Arith.ArithMulSign.Lemmas
import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Instances

open Lean Elab Tactic Meta Expr
open Smt.Reconstruction.Certifying

inductive Pol where
 | Neg : Pol
 | NZ  : Pol
 | Pos : Pol
 deriving BEq

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
    let data ← parseArithMulSign stx
    let answer ← go true data (mkConst `empty) (mkConst `empty)
    let answerType ← inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname answerType answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
where
-- acc is a partial proof corresponding to the sign of the prefix of the multiplication
  go (first : Bool) (xs : (List (Expr × Pol × Nat))) (prodSignPf : Expr) (prod : Expr) : MetaM Expr :=
    match xs with
    | [] =>
      return prodSignPf
    | (expr, pol, exp) :: t => do
      let evenExp := decide (Even exp)
      let exprType ← inferType expr
      let exprIsInt ←
        match exprType with
        | .const `Rat .. => pure false
        | .const `Int .. => pure true
        | _ => throwError "[arithMulSign]: unexpected type for expression"
      let lorInst := mkConst $
        if exprIsInt then ``lorInt else ``lorRat
      let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
      let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
      -- zero with the same type as the current argument
      let currZero := if exprIsInt then zeroI else zeroR
      let bindedType: Expr ←
        match pol with
        | Pol.Neg => mkAppM ``LT.lt #[expr, currZero]
        | Pol.NZ  => mkAppM ``Ne    #[expr, currZero]
        | Pol.Pos => mkAppM ``GT.gt #[expr, currZero]
      let expParityPf ← do
        if evenExp then
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
              if evenExp then
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
          | false, false => (exprPow, prod, exprPowSignPf, prodSignPf)
          | false, true  =>
            let prodSignPf' :=
              if prodPos then
                mkApp2 (mkConst ``castPos) prod prodSignPf
              else mkApp2 (mkConst ``castNeg) prod prodSignPf
            (exprPow, mkApp (mkConst ``Rat.ofInt) prod, exprPowSignPf, prodSignPf')
          | true, false  =>
            let exprPowSignPf' :=
              if pol == Pol.Pos || pol == Pol.NZ || evenExp then
                mkApp2 (mkConst ``castPos) exprPow exprPowSignPf
              else mkApp2 (mkConst ``castNeg) exprPow exprPowSignPf
            (mkApp (mkConst ``Rat.ofInt) exprPow, prod, exprPowSignPf', prodSignPf)
          | true, true   => (exprPow, prod, exprPowSignPf, prodSignPf)
        let answer ←
          if first then pure exprPowSignPf
          else
            if pol == Pol.Pos || pol == Pol.NZ || evenExp then
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

