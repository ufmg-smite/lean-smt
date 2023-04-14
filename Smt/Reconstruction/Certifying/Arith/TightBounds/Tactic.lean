/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas

import Mathlib.Algebra.Order.Floor
import Lean

open Lean hiding Rat
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
    let h ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← intTightMeta mvar h ``intTightUb' fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

syntax (name := intTightLb) "intTightLb" term : tactic
@[tactic intTightLb] def evalIntTightLb : Tactic := fun stx =>
  withMainContext do
    let h ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← intTightMeta mvar h ``intTightLb' fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

end Smt.Reconstruction.Certifying
