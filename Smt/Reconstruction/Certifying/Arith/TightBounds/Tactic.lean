/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas

import Lean
import Mathlib.Algebra.Order.Floor

open Lean
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying

def isIntLt : Expr → Bool
  | app (app (app (app _ (const ``Int ..)) ..) ..) .. => true
  | _ => false

def intTightMeta (mvar : MVarId) (h : Expr) (thmName outName : Name)
  : MetaM MVarId :=
  mvar.withContext do
    let t ← inferType h
    let arg ←
      if isIntLt t then
        mkAppM ``castLT #[h]
      else pure h
    let answer ← mkAppM thmName #[arg]
    let answerType ← inferType answer
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert outName answerType answer 
    return mvar'

syntax (name := intTightUb) "intTightUb" term : tactic
@[tactic intTightUb] def evalIntTightUb : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[intTightUb] start time: {← IO.monoNanosNow}ns"
    let h ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← intTightMeta mvar h ``intTightUb' fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[intTightUb] end time: {← IO.monoNanosNow}ns"

syntax (name := intTightLb) "intTightLb" term : tactic
@[tactic intTightLb] def evalIntTightLb : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[intTightLb] start time: {← IO.monoNanosNow}ns"
    let h ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← intTightMeta mvar h ``intTightLb' fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[intTightLb] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying
