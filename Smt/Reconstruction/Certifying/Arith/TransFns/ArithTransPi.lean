/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Pi.Bounds

import Smt.Reconstruction.Certifying.Util

open Lean hiding Rat
open Elab Tactic Meta

open Smt.Reconstruction.Certifying

def expr_3141592 : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero]) (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientificRat []) (.lit (.natVal 3141592)) (mkConst ``Bool.true) (.lit (.natVal 6))

def expr_3141593 : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero]) (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientificRat []) (.lit (.natVal 3141593)) (mkConst ``Bool.true) (.lit (.natVal 6))

def ratCast_lt_mpr {x y : ℚ} : x < y → (x : ℝ) < (y : ℝ) := Real.ratCast_lt.mpr

def ratOfFloat : Expr → Expr
  | .app (.app (.app (.app (.app a _) _) d) e) f =>
      .app (.app (.app (.app (.app a (mkConst ``Rat)) (mkConst ``Rat.instOfScientificRat)) d) e) f
  | e => e

def isOfNatNatLit : Expr → Bool
  | .app (.app (.app (.const ``OfNat.ofNat ..) _) _) _ => true
  | _ => false

def ratOfFloatOrNat : Expr → MetaM Expr := fun e =>
  if isOfNatNatLit e then
    mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, e, none]
  else
    pure (ratOfFloat e)

def arithTransPiMetaLt : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``LT.lt #[mkConst ``Rat, none, e, expr_3141592]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Mathlib.Meta.NormNum.normNumAt mvarTmp (← Simp.Context.mkDefault) #[]
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_lt_mpr #[val]
    let answer ← mkAppOptM ``lt_trans
      #[mkConst ``Real, none, none, none, none, val', mkConst ``Real.pi_gt_3141592]
    return answer

def arithTransPiMetaGt : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``GT.gt #[mkConst ``Rat, none, e, expr_3141593]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Mathlib.Meta.NormNum.normNumAt mvarTmp (← Simp.Context.mkDefault) #[]
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_lt_mpr #[val]
    let answer ← mkAppOptM ``gt_trans
      #[mkConst ``Real, none, none, none, none, val', mkConst ``Real.pi_lt_3141593]
    return answer

def arithTransPiMeta (mvar : MVarId) :
    Expr → Expr → Name → MetaM MVarId :=
  fun e₁ e₂ outName =>
    mvar.withContext do
      let e₁' ← ratOfFloatOrNat e₁
      let e₂' ← ratOfFloatOrNat e₂
      let val₁ ← arithTransPiMetaLt e₁'
      let val₂ ← arithTransPiMetaGt e₂'
      let answer ← mkAppM ``And.intro #[val₁, val₂]
      let goal ← inferType answer
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert outName goal answer
      return mvar'

syntax (name := arithTransPi) "arithTransPi" term "," term : tactic

@[tactic arithTransPi] def evalArithTransPi : Tactic := fun stx =>
  withMainContext do
    let e₁ ← elabTerm stx[1] none
    let e₂ ← elabTerm stx[3] none
    let mvar ← getMainGoal
    let fname ← mkFreshId
    let mvar' ← arithTransPiMeta mvar e₁ e₂ fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

example : 3.1 < Real.pi ∧ Real.pi < 4 := by
  arithTransPi 3.1 , 4

