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

#check mkApp2

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
    | (name, pol, exp) :: t => do
      let lctx ← getLCtx
      let val := (lctx.findFromUserName? name).get!.toExpr
      let evenExp := decide (Even exp)
      let valType ← inferType val
      let valIsInt ←
        match valType with
        | .const `Rat .. => pure false
        | .const `Int .. => pure true
        | _ => throwError "[arithMulSign]: unexpected type for variable"
      let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
      let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
      -- zero with the same type as the current argument
      let currZero := if valIsInt then zeroI else zeroR
      let powThm ←
        match valIsInt, evenExp with
        | false, false => pure ``powOddR
        | false, true  => pure ``powEvenR
        | true, false  => pure ``powOddI
        | true, true   => pure ``powEvenI
      let bindedType: Expr ←
        match pol with
        | false => mkAppM ``LT.lt #[val, currZero]
        | true => mkAppM ``GT.gt #[val, currZero]
      withLocalDeclD (← mkFreshId) bindedType $ fun bv => do
        let valPowSignPf ←
          if exp == 1 then
            pure bv
          else if pol then
            match valIsInt with
            | false => pure $ mkApp3 (mkConst ``powPosR) (mkNatLit exp) val bv
            | true  => pure $ mkApp3 (mkConst ``powPosI) (mkNatLit exp) val bv
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
        let valPow ←
          if exp == 1 then
            pure val
          else mkAppM ``Pow.pow #[val, mkNatLit exp]
        let prodType ←
          if first then
            pure valType
          else inferType prod
        let prodIsInt ←
          match prodType with
          | .const `Int .. => pure true
          | .const `Rat .. => pure false
          | _ => throwError "[arithMulSign]: unexpected type for accumulated product"
        let prodSignPfType ←
          if first then
            inferType valPowSignPf
          else inferType prodSignPf
        let prodPos := (← getOp prodSignPfType) == `GT.gt
        -- normalize types in case one is rat and the other is int
        let (valPow', prod', valPowSignPf', prodSignPf') :=
          match valIsInt, prodIsInt with
          | false, false => (valPow, prod, valPowSignPf, prodSignPf)
          | false, true  =>
            let prodSignPf' :=
              if prodPos then
                mkApp2 (mkConst ``castPos) prod prodSignPf
              else mkApp2 (mkConst ``castNeg) prod prodSignPf
            (valPow, mkApp (mkConst ``Rat.ofInt) prod, valPowSignPf, prodSignPf')
          | true, false  =>
            let valPowSignPf' :=
              if pol || exp % 2 == 0 then
                mkApp2 (mkConst ``castPos) valPow valPowSignPf
              else mkApp2 (mkConst ``castNeg) valPow valPowSignPf
            (mkApp (mkConst ``Rat.ofInt) valPow, prod, valPowSignPf', prodSignPf)
          | true, true   => (valPow, prod, valPowSignPf, prodSignPf)
        let answer ←
          if first then pure valPowSignPf
          else
            if pol || exp % 2 == 0 then
              if prodPos then
                mkAppOptM ``combineSigns₁ #[none, none, valPow', prod', valPowSignPf', prodSignPf']
              else mkAppOptM ``combineSigns₂ #[none, none, valPow', prod', valPowSignPf', prodSignPf']
            else
              if prodPos then
                mkAppOptM ``combineSigns₃ #[none, none, valPow', prod', valPowSignPf', prodSignPf']
              else mkAppOptM ``combineSigns₄ #[none, none, valPow', prod', valPowSignPf', prodSignPf']
        let prod' ←
          if first then
            pure valPow
          else mkAppM ``Mul.mul #[prod', valPow']
        let rc ← go false t xs' answer prod'
        mkLambdaFVars #[bv] rc

example (a : Int) : a > 0 → a ^ 2 > 0 := by
  arithMulSign [a], [1], [2]

example (a : Int) : a < 0 → a ^ 3 < 0 := by
  arithMulSign [a], [-1], [3]

example (a b : ℚ) : a > 0 → b < 0 → a ^ 2 * b ^ 3 < 0 := by
  arithMulSign [a,b], [1,-1], [2,3]

example (a b c d e : Int) : a < 0 → b > 0 → c < 0 → d > 0 → e < 0 → a * (b ^ 2) * (c ^ 2) * (d ^ 4) * (e ^ 5) > 0 := by
  arithMulSign [a,b,c,d,e], [-1,1,-1,1,-1], [1,2,2,4,5]

example (a : Int) (b : ℚ) : a < 0 → b < 0 → a ^ 3 * b ^ 3 > 0 := by
  arithMulSign [a,b], [-1,-1], [3,3]

example (a e : Int) (b c d : ℚ) : a < 0 → b > 0 → c < 0 → d > 0 → e < 0 → a * (b ^ 2) * (c ^ 2) * (d ^ 4) * (e ^ 5) > 0 := by
  arithMulSign [a,b,c,d,e], [-1,1,-1,1,-1], [1,2,2,4,5]
