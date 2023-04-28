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
  go (first : Bool) (xs xs' : MulSignInput) (acc : Expr) (prod : Expr) : MetaM Expr :=
    match xs with
    | [] =>
      return acc
    | (name, pol, exp) :: t => do
      let lctx ← getLCtx
      let val := (lctx.findFromUserName? name).get!.toExpr
      let evenExp := decide (Even exp)
      let valType ← inferType val
      let isInt ←
        match valType with
        | .const `Rat .. => pure false
        | .const `Int .. => pure true
        | _ => throwError "[arithMulSign]: unexpected type for variable"
      let zeroI := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
      let zeroR := mkApp (mkConst ``Rat.ofInt) zeroI
      -- zero with the same type as the current argument
      let currZero := if isInt then zeroI else zeroR
      let powThm ←
        match isInt, evenExp with
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
            match isInt with
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
        let acc' ←
          if first then pure valPowSignPf
          else
            let accType ← inferType acc
            let valPos := (← getOp accType) == `GT.gt
            if pol then
              if valPos then
                mkAppOptM ``combineSigns₁ #[none, none, valPow, prod, valPowSignPf, acc]
              else mkAppOptM ``combineSigns₂ #[none, none, valPow, prod, valPowSignPf, acc]
            else
              if valPos then
                mkAppOptM ``combineSigns₃ #[none, none, valPow, prod, valPowSignPf, acc]
              else mkAppOptM ``combineSigns₄ #[none, none, valPow, prod, valPowSignPf, acc]
        let prod' ←
          if first then
            pure valPow
          else mkAppM ``Mul.mul #[prod, valPow]
        let rc ← go false t xs' acc' prod'
        mkLambdaFVars #[bv] rc

example (a : Int) : a > 0 → a ^ 2 > 0 := by
  arithMulSign [a], [1], [2]

example (a : Int) : a < 0 → a ^ 3 < 0 := by
  arithMulSign [a], [-1], [3]

example (a b : ℚ) : a > 0 → b < 0 → a ^ 2 * b ^ 3 < 0 := by
  arithMulSign [a,b], [1,-1], [2,3]

example (a b c d e : Int) : a < 0 → b > 0 → c < 0 → d > 0 → e < 0 → a * (b ^ 2) * (c ^ 3) * (d ^ 4) * (e ^ 5) < 0 := by
  arithMulSign [a,b,c,d,e], [-1,1,-1,1,-1], [1,2,3,4,5]
