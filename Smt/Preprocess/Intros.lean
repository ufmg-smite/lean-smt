/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Basic
import Lean.Meta.Tactic.Assert

namespace Smt.Preprocess

open Lean

/-- Returns `true` if `fv` corresponds to a proposition in the local context. -/
def isPropHyp (fv : FVarId) : MetaM Bool := do
  let localDecl ← fv.getDecl
  unless localDecl.isImplementationDetail do
    if ← pure !(isNonEmpty localDecl.type) <&&> Meta.isProp localDecl.type then
      return true
  return false
where
  isNonEmpty (e : Expr) : Bool :=
  match e with
  | .app (.const ``Nonempty _) _ => true
  | .forallE _ _ b _ => isNonEmpty b
  | _ => false

def intros (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let (fvs, mv) ← mv.intros
  let hfvs := fvs.map Expr.fvar
  return { map := Std.HashMap.insertMany {} (hfvs.zip (hfvs.map (#[·]))), hs := hs ++ hfvs, mv }

end Smt.Preprocess
