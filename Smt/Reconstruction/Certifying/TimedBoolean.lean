import Lean

import Smt.Reconstruction.Certifying.Boolean

open Lean Elab.Tactic
open Meta hiding contradiction

open Smt.Reconstruction.Certifying

set_option trace.smt.profile true

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

variable {s : Syntax}

syntax (name := timed) "timed" term : tactic
@[tactic timed] def evalTimed : Tactic := fun stx => do
  if stx[1].getNumArgs > 0 then
    trace[smt.profile] s!"[{stx[1][0]}] start time: {← IO.monoNanosNow}ns"
  else
    trace[smt.profile] s!"[{stx[1]}] start time: {← IO.monoNanosNow}ns"
  let tstx : Term := ⟨stx[1]⟩
  evalTactic (← `(tactic| exact $tstx))
  if stx[1].getNumArgs > 0 then
    trace[smt.profile] s!"[{stx[1][0]}]  end time: {← IO.monoNanosNow}ns"
  else
    trace[smt.profile] s!"[{stx[1]}] start time: {← IO.monoNanosNow}ns"

example (a b : Prop) : ¬ (a → b) → a := by
  intro h
  timed notImplies1 h

example (a b : Prop) : a = a := by
  have h : b = b := by timed rfl
  timed rfl

