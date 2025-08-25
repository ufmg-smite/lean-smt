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
  match_expr e with
  | Nonempty _ => true
  | _ => false

end Smt.Preprocess
