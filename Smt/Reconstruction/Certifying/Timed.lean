import Lean

import Smt.Reconstruction.Certifying.Boolean

open Lean Elab.Tactic
open Meta hiding contradiction

open Smt.Reconstruction.Certifying

set_option trace.smt.profile true

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
    trace[smt.profile] s!"[{stx[1]}] end time: {← IO.monoNanosNow}ns"

example (a b : Prop) : ¬ (a → b) → a := by
  intro h
  timed notImplies1 h

example (a b : Prop) : a = a := by
  have _ : b = b := by timed rfl
  timed rfl

