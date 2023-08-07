import Lean

import Smt.Reconstruction.Certifying.Boolean

open Lean Elab.Tactic

open Smt.Reconstruction.Certifying

#check notImplies1

syntax (name := notImplies1T) "notImplies1T" term : tactic

@[tactic notImplies1T] def evalNotImplies1 : Tactic := fun stx => do
  trace[smt.profile] m!"[notImplies1] start time: {← IO.monoNanosNow}ns"
  trace[smt.profile] m!"[notImplies1] end time: {← IO.monoNanosNow}ns"

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
