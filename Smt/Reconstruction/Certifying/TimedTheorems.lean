/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Factor
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta

namespace Smt.Reconstruction.Certifying

syntax (name := cnfAndNegT) "cnfAndNegT" ("[" term,* "]")? : tactic

def parseCnfAndNeg : Syntax → TacticM Expr
  | `(tactic| cnfAndNegT [ $[$hs],* ]) => do
    let each ← Array.mapM (fun h => elabTerm h none) hs
    let li := listExpr each.data (Expr.sort Level.zero)
    return li
  | _ => throwError "[cnfAndNeg]: wrong usage"

@[tactic cnfAndNegT] def evalCnfAndNegT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let e ← parseCnfAndNeg stx
    closeMainGoal (mkApp (mkConst ``cnfAndNeg) e)
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[cnfAndNeg] Time taken: {endTime - startTime}ms"

syntax (name := cnfAndPosT) "cnfAndPosT" ("[" term,* "]")? "," term : tactic

def parseCnfAndPos : Syntax → TacticM (Expr × Expr)
  | `(tactic| cnfAndPosT [ $[$hs],* ], $i) => do
    let each ← Array.mapM (fun h => elabTerm h none) hs
    let li := listExpr each.data (Expr.sort Level.zero)
    let i' ← elabTerm i none
    return (li, i')
  | _ => throwError "[cnfAndPos]: wrong usage"

@[tactic cnfAndPosT] def evalCnfAndPosT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let (li, i) ← parseCnfAndPos stx
    closeMainGoal $ mkApp (mkApp (mkConst ``cnfAndPos) li) i
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[cnfAndPos]: Time taken: {endTime - startTime}ms"

syntax (name := congrT) "congrT" term "," term : tactic
@[tactic congrT] def evalCongrT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let h₁ := ⟨stx[1]⟩
    let h₂ := ⟨stx[3]⟩
    evalTactic (← `(tactic| exact congr $h₁ $h₂))
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[congrT]: Time taken: {endTime - startTime}ms"

syntax (name := andElimT) "andElimT" term "," term : tactic
@[tactic andElimT] def evalAndElimT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  evalAndElim stx
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[andElimT] Time taken: {endTime - startTime}ms"

syntax (name := notOrElimT) "notOrElimT" term "," term : tactic
@[tactic notOrElimT] def evalNotOrElimT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  evalNotOrElim stx
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[notOrElimT] Time taken: {endTime - startTime}ms"

syntax (name := factorT) "factorT" term ("," term)? : tactic

@[tactic factorT] def evalFactorT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  evalFactor stx
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[factor] Time taken: {endTime - startTime}ms"

end Smt.Reconstruction.Certifying
