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
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero]) (mkConst ``Real) (mkConst ``inferInstance) (mkNatLit 3141593) (mkConst ``True) (mkNatLit 6)

def ff {x y : ℚ} : x < y → (x : ℝ) < (y : ℝ) := Real.ratCast_lt.mpr

def ratOfFloat : Expr → Expr
  | .app (.app (.app (.app (.app a _) _) d) e) f =>
      .app (.app (.app (.app (.app a (mkConst ``Rat)) (mkConst ``Rat.instOfScientificRat)) d) e) f
  | e => e

def isOfNatNatLit : Expr → Bool
  | .app (.app (.app (.const ``OfNat.ofNat ..) _) _) _ => true
  | _ => false

def arithTransPiMeta (mvar : MVarId) : Expr → Expr → MetaM (List MVarId) := fun e₁ e₂ =>
  mvar.withContext do
    let e₁' ←
      if isOfNatNatLit e₁ then
        mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, e₁, none]
      else
        pure (ratOfFloat e₁)
    let goal ← mkAppOptM ``LT.lt #[mkConst ``Rat, none, e₁', expr_3141592]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Mathlib.Meta.NormNum.normNumAt mvarTmp (← Simp.Context.mkDefault) #[]
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ff #[val]
    let answer ← mkAppOptM ``lt_trans #[mkConst ``Real, none, none, none, none, val', mkConst ``Real.pi_gt_3141592]
    let tt ← inferType answer
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert (Name.mkSimple "bleh") tt answer
    return [mvar']

syntax (name := arithTransPi) "arithTransPi" term "," term : tactic

@[tactic arithTransPi] def evalArithTransPi : Tactic := fun stx =>
  withMainContext do
    let t₁ ← elabTerm stx[1] none
    let t₂ ← elabTerm stx[3] none
    let mvar ← getMainGoal
    let mvar' ← arithTransPiMeta mvar t₁ t₂
    replaceMainGoal mvar'


example : 3.1 < Real.pi := by
  arithTransPi 3.1 , 4
  exact bleh
  /- exact bleh -/

