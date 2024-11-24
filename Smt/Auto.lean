/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Auto.Tactic
import Smt.Tactic.Smt

open Lean in
def smtSolverFunc (ls : Array Auto.Lemma) (is : Array Auto.Lemma) : MetaM Expr := do
  let fi l := do
    let userName ← mkFreshUserName `inst
    let type ← Meta.mkAppM ``Inhabited #[l.type]
    let value ← Meta.mkAppOptM ``Inhabited.mk #[l.type, l.proof]
    return { userName, type, value }
  let is ← is.mapM fi
  let fl l := do
    let userName ← mkFreshUserName `h
    let type ← Auto.Lam2D.approxSimpNF l.type
    let value := l.proof
    return { userName, type, value }
  let ls ← ls.mapM fl
  let h ← Meta.mkFreshExprMVar (Expr.const ``False [])
  let (_, mv) ← h.mvarId!.assertHypotheses is
  let (fvs, mv) ← mv.assertHypotheses ls
  mv.withContext do
    let hs := fvs.map (.fvar ·)
    _ ← Smt.smt mv hs.toList
    -- Note: auto should allow solvers to export new goals to users
    -- for mv in mvs do
    --   logInfo m!"new : {mv}"
    instantiateMVars h

attribute [rebind Auto.Native.solverFunc] smtSolverFunc
