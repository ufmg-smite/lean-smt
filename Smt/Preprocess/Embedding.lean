import Lean.Meta.Tactic.Simp
import Smt.Preprocess.Basic
import Smt.Preprocess.Embedding.Attribute

private def Lean.Expr.contains (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

namespace Smt.Preprocess

open Lean

def hasType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ t b _ => p t || hasType b p
  | _                => p e

def hasReturnType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ _ b _ => hasReturnType b p
  | _                => p e

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let ⟨_, _, fvs⟩ := (ts.push (← mv.getType)).foldl Lean.collectFVars {}
  let fvs ← Meta.sortFVarIds fvs
  -- Check if we need to do anything.
  let bts := if (← getEnv).contains `Real then  #[``Nat, ``Rat, ``Bool] else #[``Nat, ``Bool]
  let fvts ← fvs.mapM FVarId.getType
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains ((bts.map (.const · [])).contains ·)) then
    return ⟨{}, hs, mv⟩
  -- Find the embedding simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `embedding | throwError "embedding simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `embedding | throwError "embedding simproc extension not found"
  let simpTheorems := #[← thmsExt.getTheorems]
  let simpProcs := #[← procsExt.getSimprocs]
  -- Assert all hypotheses that are not free vars.
  let hsts := (hs.zip ts).filter fun (h, _) => !h.isFVar
  let as : Array Meta.Hypothesis := hsts.map fun (h, t) => { userName := .anonymous, type := t, value := h }
  let (as, mv) ← mv.assertHypotheses as
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hsts.findIdx? (·.fst == h) with
    | some idx => map.insert h (.fvar as[idx]!)
    | none => map.insert h h
  -- Revert free vars in `hs` and `mv`.
  let (fvs, mv) ← mv.revert fvs true
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext {} simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- Extend `fvs` to account for `nonneg` assumptions.
  let bts := bts.pop -- Do not consider `Bool` for assumptions.
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    if hasReturnType t ((bts.map (.const · [])).contains ·) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
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
