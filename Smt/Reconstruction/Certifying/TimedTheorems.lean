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

syntax (name := notImplies1T) "notImplies1T" term : tactic
@[tactic notImplies1T] def evalNotImplies1 : Tactic := fun stx => do
  trace[smt.profile] m!"[notImplies1] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    logInfo m!"stx = {stx}"
    let z := stx.getArgs
    let z' : Array Syntax := {
      data := z.data.tail
    }
    let stx' := mkNode ``Parser.Term.term z'
    logInfo m!"stx' = {stx'}"
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notImplies1 #[h])
  trace[smt.profile] m!"[notImplies1] end time: {← IO.monoNanosNow}ns"

set_option pp.rawOnError true
example (a b : Prop) : ¬ (a → b) → a := by
  intro h
  notImplies1T h

syntax (name := notImplies2T) "notImplies2T" term : tactic
@[tactic notImplies2T] def evalNotImplies2 : Tactic := fun stx => do
  trace[smt.profile] m!"[notImplies2] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notImplies2 #[h])
  trace[smt.profile] m!"[notImplies2] end time: {← IO.monoNanosNow}ns"

syntax (name := equivElim1T) "equivElim1T" term : tactic
@[tactic equivElim1T] def evalEquivElim1 : Tactic := fun stx => do
  trace[smt.profile] m!"[equivElim1T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``equivElim1 #[h])
  trace[smt.profile] m!"[equivElim1T] end time: {← IO.monoNanosNow}ns"

syntax (name := equivElim2T) "equivElim2T" term : tactic
@[tactic equivElim2T] def evalEquivElim2 : Tactic := fun stx => do
  trace[smt.profile] m!"[equivElim2T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``equivElim2 #[h])
  trace[smt.profile] m!"[equivElim2T] end time: {← IO.monoNanosNow}ns"

syntax (name := notEquivElim1T) "notEquivElim1T" term : tactic
@[tactic notEquivElim1T] def evalNotEquivElim1 : Tactic := fun stx => do
  trace[smt.profile] m!"[notEquivElim1T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notEquivElim1 #[h])
  trace[smt.profile] m!"[notEquivElim1T] end time: {← IO.monoNanosNow}ns"

syntax (name := notEquivElim2T) "notEquivElim2T" term : tactic
@[tactic notEquivElim2T] def evalNotEquivElim2 : Tactic := fun stx => do
  trace[smt.profile] m!"[notEquivElim2T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notEquivElim2 #[h])
  trace[smt.profile] m!"[notEquivElim2T] end time: {← IO.monoNanosNow}ns"

syntax (name := iteElim1T) "iteElim1T" term : tactic
@[tactic iteElim1T] def evalIteElim1T : Tactic := fun stx => do
  trace[smt.profile] m!"[iteElim1T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``iteElim1 #[h])
  trace[smt.profile] m!"[iteElim1T] end time: {← IO.monoNanosNow}ns"

syntax (name := iteElim2T) "iteElim2T" term : tactic
@[tactic iteElim2T] def evalIteElim2T : Tactic := fun stx => do
  trace[smt.profile] m!"[iteElim2T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``iteElim2 #[h])
  trace[smt.profile] m!"[iteElim2T] end time: {← IO.monoNanosNow}ns"

syntax (name := notIteElim1T) "notIteElim1T" term : tactic
@[tactic notIteElim1T] def evalNotIteElim1T : Tactic := fun stx => do
  trace[smt.profile] m!"[notIteElim1T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notIteElim1T #[h])
  trace[smt.profile] m!"[notIteElim1T] end time: {← IO.monoNanosNow}ns"

syntax (name := notIteElim2T) "notIteElim2T" term : tactic
@[tactic notIteElim2T] def evalNotIteElim2T : Tactic := fun stx => do
  trace[smt.profile] m!"[notIteElim2T] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``notIteElim2T #[h])
  trace[smt.profile] m!"[notIteElim2T] end time: {← IO.monoNanosNow}ns"

syntax (name := contradictionT) "contradictionT" term "," term : tactic
@[tactic contradictionT] def evalContradictionT : Tactic := fun stx => do
  trace[smt.profile] m!"[contradictionT] end time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    closeMainGoal (← mkAppM ``contradiction #[h₁, h₂])
  trace[smt.profile] m!"[contradictionT] end time: {← IO.monoNanosNow}ns"

syntax (name := orCommT) "orCommT" term : tactic
@[tactic orCommT] def evalOrCommT : Tactic := fun stx => do
  trace[smt.profile] m!"[orCommT] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``orComm #[h])
  trace[smt.profile] m!"[orCommT] end time: {← IO.monoNanosNow}ns"

syntax (name := orAssocDirT) "orAssocDirT" term : tactic
@[tactic orAssocDirT] def evalOrAssocDirT : Tactic := fun stx => do
  trace[smt.profile] m!"[orAssocDirT] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``orAssocDir #[h])
  trace[smt.profile] m!"[orAssocDirT] end time: {← IO.monoNanosNow}ns"

syntax (name := orAssocConvT) "orAssocConvT" term : tactic
@[tactic orAssocConvT] def evalOrAssocConvT : Tactic := fun stx => do
  trace[smt.profile] m!"[orAssocConvT] start time: {← IO.monoNanosNow}ns"
  withMainContext do
    let h ← elabTerm stx[1] none
    closeMainGoal (← mkAppM ``orAssocConv #[h])
  trace[smt.profile] m!"[orAssocConvT] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying
