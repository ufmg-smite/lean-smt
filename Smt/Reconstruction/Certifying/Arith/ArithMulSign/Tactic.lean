import Lean

import Mathlib.Data.Nat.Parity

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Arith.ArithMulSign.Lemmas

open Lean Elab Tactic Meta Expr
open Smt.Reconstruction.Certifying

abbrev MulSignInput := List (Expr × Bool × Nat)

--              var names/neg or pos/ exponents
-- arithMulSign [a, b, c] [1, -1, 1], [2, 3, 1]
syntax (name := arithMulSign) "arithMulSign" ("[" term,* "]")? "," ("[" term,* "]") "," ("[" term,* "]")? : tactic

def parseArithMulSign : Syntax → TacticM MulSignInput
  | `(tactic| arithMulSign [ $[$ns],* ], [ $[$bs],* ], [ $[$es],* ]) => do
    let exprs: List Expr ←
      ns.toList.mapM (fun h: Term => elabTerm h none)
    let bools: List Bool ←
      bs.toList.mapM (fun h: Term => do
                      let hExpr ← elabTerm h none
                      let o := getNatLit? hExpr
                      pure $ Option.isSome o
                    )
    let exps : List Nat ← es.toList.mapM stxToNat
    pure (exprs.zip (bools.zip exps))
  | _ => throwError "[ArithMulSign]: wrong syntax"

@[tactic arithMulSign] def evalArithMulSign : Tactic := fun stx =>
  withMainContext do
    let data ← parseArithMulSign stx
    let mvar ← getMainGoal
    mvar.withContext do
      let answer ← go true data data (mkConst `empty) (mkConst `empty)
      let answerType ← inferType answer
      let fname ← mkFreshId
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname answerType answer
      replaceMainGoal [mvar']
      evalTactic (← `(tactic| exact $(mkIdent fname)))
where
-- acc is a partial proof corresponding to the sign of the prefix of the multiplication
  go (first : Bool) (xs xs' : MulSignInput) (prodSignPf : Expr) (prod : Expr) : MetaM Expr :=
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
        | _ => throwError "[arithMulSign]: unexpected type for variable"
      let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
      let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
      -- zero with the same type as the current argument
      let currZero := if exprIsInt then zeroI else zeroR
      let powThm ←
        match exprIsInt, evenExp with
        | false, false => pure ``powOddR
        | false, true  => pure ``powEvenR
        | true, false  => pure ``powOddI
        | true, true   => pure ``powEvenI
      let bindedType: Expr ←
        match pol with
        | false => mkAppM ``LT.lt #[expr, currZero]
        | true => mkAppM ``GT.gt #[expr, currZero]
      withLocalDeclD (← mkFreshId) bindedType $ fun bv => do
        let exprPowSignPf ←
          if exp == 1 then
            pure bv
          else if pol then
            match exprIsInt with
            | false => pure $ mkApp3 (mkConst ``powPosR) (mkNatLit exp) expr bv
            | true  => pure $ mkApp3 (mkConst ``powPosI) (mkNatLit exp) expr bv
          else
            if evenExp then
              let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 0)]
              let iffExp := mkApp (mkConst ``Nat.even_iff) (mkNatLit exp)
              let evenExp ← mkAppM ``Iff.mpr #[iffExp, rflExpr]
              mkAppM powThm #[bv, evenExp]
            else
              let rflExpr ← mkAppOptM ``rfl #[(mkConst ``Nat), (mkNatLit 1)]
              let iffExp := mkApp (mkConst ``Nat.odd_iff) (mkNatLit exp)
              let oddExp ← mkAppM ``Iff.mpr #[iffExp, rflExpr]
              mkAppM powThm #[bv, oddExp]
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
              if pol || exp % 2 == 0 then
                mkApp2 (mkConst ``castPos) exprPow exprPowSignPf
              else mkApp2 (mkConst ``castNeg) exprPow exprPowSignPf
            (mkApp (mkConst ``Rat.ofInt) exprPow, prod, exprPowSignPf', prodSignPf)
          | true, true   => (exprPow, prod, exprPowSignPf, prodSignPf)
        let answer ←
          if first then pure exprPowSignPf
          else
            if pol || exp % 2 == 0 then
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
        let rc ← go false t xs' answer prod'
        mkLambdaFVars #[bv] rc

