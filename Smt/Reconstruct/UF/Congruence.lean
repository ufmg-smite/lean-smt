/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

open Lean Elab Tactic Meta

namespace Smt.Reconstruct.UF

def rewriteHyp (hyp : Expr) (mv : MVarId) : MetaM MVarId :=
  mv.withContext do
    let type ← mv.getType
    let r ← mv.rewrite type hyp
    mv.replaceTargetEq r.eNew r.eqProof

def smtCongr (mv : MVarId) (hyps : Array Expr) : MetaM Unit := do
  let mv ← hyps.foldrM rewriteHyp mv
  mv.refl

namespace Tactic

syntax (name := smtCongr) "smtCongr"  ("[" term,* "]")? : tactic

def termToSyntax : Term → TacticM Syntax := fun t => pure t

def parseSmtCongr : Syntax → TacticM (Array Expr)
  | `(tactic| smtCongr  [ $[$hs],* ]) => withMainContext do
    let hs' : Array Syntax ← hs.mapM termToSyntax
    hs'.mapM (elabTerm · none)
  | _ => throwError "[smtCongr]: invalid Syntax"

@[tactic smtCongr] def evalSmtCongr : Tactic := fun stx => do
  let es ← parseSmtCongr stx
  UF.smtCongr (← getMainGoal) es

example (a b c d : Int) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

end Smt.Reconstruct.UF.Tactic
