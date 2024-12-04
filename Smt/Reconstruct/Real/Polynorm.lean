/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Zify

namespace Smt.Reconstruct.Real

open Lean

open Lean Mathlib.Tactic.RingNF in
/-- Use `arithPolyNormCore` to rewrite the main goal. -/
def polyNormCore (mv : MVarId) : MetaM (Option MVarId) := mv.withContext do
  let tgt ← instantiateMVars (← mv.getType)
  let s ← IO.mkRef {}
  let r ← M.run s {} <| rewrite tgt
  if r.expr.consumeMData.isConstOf ``True then
    mv.assign (← Meta.mkOfEqTrue (← r.getProof))
    return none
  else
    Meta.applySimpResultToTarget mv tgt r

def traceArithPolyNorm (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

/-- Use `arithPolyNorm` to rewrite the main goal. -/
def polyNorm (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.arithPolyNorm traceArithPolyNorm do
  mv.withContext do
  let some zifySimps ← Meta.getSimpExtension? `zify_simps | throwError "zify_simps simp set is not available"
  let some pushCast ← Meta.getSimpExtension? `push_cast | throwError "push_cast simp set is not available"
  let ctx := { config := { decide := false },  simpTheorems := #[← zifySimps.getTheorems, ← pushCast.getTheorems] }
  let (some mv, _) ← Meta.simpTarget mv ctx | throwError "simp failed"
  mv.withContext do
  if let .some mv ← polyNormCore mv then
    throwError "[arithPolyNorm]: could not prove {← mv.getType}"

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  if let some (_, mv) ← normNumAt mv {} #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.polyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Real.Tactic

example (x y z : Real) : 1 * (x + y) * z / 4  = 1/(2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm
