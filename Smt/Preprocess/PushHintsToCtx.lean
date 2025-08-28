/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Basic
import Lean.Meta.Tactic.Assert

namespace Smt.Preprocess

open Lean

def pushHintsToCtx (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  hs.foldrM pushHint { map := {}, hs := #[], mv }
where
  pushHint (h : Expr) (r : Result) : MetaM Result := do
    if h.isFVar || h.isConst then
      return { r with map := r.map.insert h #[h], hs := r.hs.push h }
    else
      let mv' ← r.mv.assert (← mkFreshId) (← Meta.inferType h) h
      let ⟨fv, mv'⟩ ← mv'.intro1
      let h' := .fvar fv
      return { map := r.map.insert h' #[h], hs := r.hs.push h', mv := mv' }

end Smt.Preprocess
