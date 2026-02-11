/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Intro

namespace Smt.Preprocess

open Lean

def negateGoal (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let target ← mv.getType
  if target.isFalse then return { map := {}, hs, mv }
  let [mv] ← mv.applyConst ``Classical.byContradiction
    | throwError "[negateGoal] Unexpected result after applying {``Classical.byContradiction}"
  let (fv, mv) ← mv.intro1
  return { map := Std.HashMap.insert {} (.fvar fv) #[.fvar fv], hs := hs.push (.fvar fv), mv }

end Smt.Preprocess
