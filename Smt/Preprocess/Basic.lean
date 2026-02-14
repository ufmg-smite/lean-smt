/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Smt.Preprocess

open Lean

structure Result where
  map : Std.HashMap Expr (Array Expr)
  hs : Array Expr
  mv : MVarId

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      if ← pure !(isNonEmpty localDecl.type) <&&> Meta.isProp localDecl.type then
        result := result.push localDecl.fvarId
  return result
where
  isNonEmpty (e : Expr) : Bool :=
  match e with
  | .app (.const ``Nonempty _) _ => true
  | .forallE _ _ b _ => isNonEmpty b
  | _ => false

def traceApplySteps (r : Except Exception Result) : MetaM MessageData :=
  return match r with
    | .ok r    => m!"after steps: {r.mv}"
    | .error _ => m!"{bombEmoji}"

def applySteps (mv : MVarId) (hs : Array Expr) (steps : Array (MVarId → Array Expr → MetaM Result)) : MetaM Result :=
  withTraceNode `smt.preprocess traceApplySteps do
  if h : 0 < steps.size then
    let mut { map, hs, mv } ← steps[0] mv hs
    for step in steps[1:] do
      let ⟨map', hs', mv'⟩ ← step mv hs
      map := compose map map'
      hs := hs'
      mv := mv'
    return { map, hs, mv }
  else
    return Result.mk {} #[] mv
where
  compose (m₁ m₂ : Std.HashMap Expr (Array Expr)) : Std.HashMap Expr (Array Expr) :=
    m₂.fold (init := m₁) fun map k v =>
      map.insert k (v.map fun x => m₁.getD x #[x]).flatten

end Smt.Preprocess
