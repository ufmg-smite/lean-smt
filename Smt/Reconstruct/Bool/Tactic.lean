/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Reconstruct.Bool.Lemmas

namespace Smt.Reconstruct.Bool

open Lean

def traceBoolify (r : Except Exception MVarId) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def boolify (mv : MVarId) : MetaM MVarId := withTraceNode `smt.reconstruct.boolify traceBoolify do
  let ns := [``Bool.decide_eq_true, ``decide_true_eq, ``decide_false_eq, ``decide_not_eq, ``decide_and_eq, ``decide_or_eq, ``decide_eq_eq, ``decide_xor_eq]
  let simpTheorems ← ns.foldrM (fun n a => a.addTheorem (.decl n) (.const n [])) {}
  let (some mv, _) ← Meta.simpTarget mv { simpTheorems } | throwError "failed to boolify goal:{mv}"
  return mv

namespace Tactic

syntax (name := boolify) "boolify" : tactic

open Lean.Elab Tactic in
@[tactic boolify] def evalBoolify : Tactic := fun _ => withMainContext do
  let mv ← Tactic.getMainGoal
  let mv ← Bool.boolify mv
  replaceMainGoal [mv]

end Smt.Reconstruct.Bool.Tactic
