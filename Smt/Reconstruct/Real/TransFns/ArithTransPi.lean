/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule14ARITH_TRANS_PIE
-/

import Lean
import Qq
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

import Smt.Reconstruct.Util
import Smt.Reconstruct.Real.Polynorm

open Lean Qq
open Elab Tactic Meta

open Real

namespace Smt.Reconstruct.Real.TransFns

def expr_pi_upper : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero])
    (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientific [])
    (.lit (.natVal 314159265358979323847)) (mkConst ``Bool.true) (.lit (.natVal 20))

def expr_pi_lower : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero])
    (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientific [])
    (.lit (.natVal 314159265358979323846)) (mkConst ``Bool.true) (.lit (.natVal 20))

theorem ratCast_le {x y : ℚ} : x ≤ y → (x : ℝ) ≤ (y : ℝ) :=
  Rat.cast_le.mpr

def ratOfFloat : Expr → Expr
  | .app (.app (.app (.app (.app a _) _) d) e) f =>
      .app (.app (.app (.app (.app a (mkConst ``Rat)) (mkConst ``Rat.instOfScientific)) d) e) f
  | e => e

def isOfNatNatLit : Expr → Bool
  | .app (.app (.app (.const ``OfNat.ofNat ..) _) _) _ => true
  | _ => false

def ratOfFloatOrNat : Expr → MetaM Expr := fun e =>
  if isOfNatNatLit e then
    mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, e, none]
  else
    pure (ratOfFloat e)

def arithTransPiMetaLe : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``LE.le #[mkConst ``Rat, none, e, expr_pi_lower]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Real.normNum mvarTmp
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_le #[val]
    let answer ← mkAppOptM ``le_trans
      #[mkConst ``Real, none, none, none, none, val', q(le_of_lt pi_gt_d20)]
    return answer

-- Assumes `e` is a real variable
def arithTransPiMetaLeReal : Expr → MetaM Expr :=
  fun e => do
    let expr_pi_lower_real ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, expr_pi_lower]
    let goal ← mkAppOptM ``LE.le #[mkConst ``Real, none, e, expr_pi_lower_real]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Real.normNum mvarTmp
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let answer ← mkAppOptM ``le_trans
      #[mkConst ``Real, none, none, none, none, val, q(le_of_lt pi_gt_d20)]
    return answer

def arithTransPiMetaGe : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``GE.ge #[mkConst ``Rat, none, e, expr_pi_upper]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Real.normNum mvarTmp
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_le #[val]
    let answer ← mkAppOptM ``ge_trans
      #[mkConst ``Real, none, none, none, none, val', q(le_of_lt pi_lt_d20)]
    return answer

-- Assumes `e` is a real variable
def arithTransPiMetaGeReal : Expr → MetaM Expr :=
  fun e => do
    let expr_pi_upper_real ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, expr_pi_upper]
    let goal ← mkAppOptM ``GE.ge #[mkConst ``Real, none, e, expr_pi_upper_real]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Real.normNum mvarTmp
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let answer ← mkAppOptM ``ge_trans
      #[mkConst ``Real, none, none, none, none, val, q(le_of_lt pi_lt_d20)]
    return answer

def arithTransPiSolve (l u : Expr) : MetaM Expr := do
  let l' ← ratOfFloatOrNat l
  let u' ← ratOfFloatOrNat u
  let val₁ ← arithTransPiMetaLe l'
  let val₂ ← arithTransPiMetaGe u'
  mkAppM ``And.intro #[val₁, val₂]

def arithTransPiMeta (mvar : MVarId) : Expr → Expr → Name → MetaM MVarId :=
  fun e₁ e₂ outName => mvar.withContext do
    let answer ← arithTransPiSolve e₁ e₂
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

example : 3.1415926535 ≤ Real.pi ∧ Real.pi ≤ 3.1415926536 := by
  arithTransPi 3.1415926535 , 3.1415926536

def arithTransPiTac (mvar : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← mvar.getType
  match t with
  | ~q(Real.pi ≥ $l ∧ Real.pi ≤ $u) =>
    let val₁ ← arithTransPiMetaLeReal l
    let val₂ ← arithTransPiMetaGeReal u
    let answer ← mkAppM ``And.intro #[val₁, val₂]
    mvar.assign answer
  | _ => throwError "[arithTransPiTac] Unexpected pattern for input metavariable"

end Smt.Reconstruct.Real.TransFns
