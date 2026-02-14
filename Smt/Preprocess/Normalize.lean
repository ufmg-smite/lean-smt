/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Meta.Tactic.Simp
import Smt.Preprocess.Basic
import Smt.Preprocess.Normalize.Attribute

namespace Smt.Preprocess

open Lean

def normalize (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find the smt_normalize simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `smt_normalize | throwError "smt_normalize simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `smt_normalize | throwError "smt_normalize simproc extension not found"
  let simpTheorems := #[← thmsExt.getTheorems]
  let simpProcs := #[← procsExt.getSimprocs]
  -- Assert all hypotheses that are not free vars.
  let (hs₁, hs₂) := hs.partition Expr.isFVar
  let ts₂ ← hs₂.mapM Meta.inferType
  let as₂ : Array Meta.Hypothesis := (hs₂.zip ts₂).map fun (h', t') => { userName := .anonymous, type := t', value := h' }
  let (fvs₂, mv) ← mv.assertHypotheses as₂
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hs₂.findIdx? (· == h) with
    | some idx => map.insert h (.fvar fvs₂[idx]!)
    | none => map.insert h h
  -- Revert all hypotheses in `mv`'s context.
  let fvs ← Meta.sortFVarIds (hs₁.map Expr.fvarId! ++ fvs₂)
  let (fvs', mv) ← mv.revert fvs true
  -- Simplify the goal using the smt_normalize theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[smt_normalize] simplification failed"
  -- Re-introduce all free vars.
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  let inverseMap₂ := Std.HashMap.ofList ((fvs'.zip fvs'').map fun (of, to) => (.fvar of, .fvar to)).toList
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs.map fun h => inverseMap[h]?.getD h
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

end Smt.Preprocess
