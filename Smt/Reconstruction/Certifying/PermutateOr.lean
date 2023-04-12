/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Pull
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic

namespace Smt.Reconstruction.Certifying

def permutateOrMeta (mvar : MVarId) (val : Expr) (perm : List Nat)
  (suffIdx : Option Nat) (name : Name) : MetaM MVarId :=
  mvar.withContext do
    let type ← instantiateMVars (← Meta.inferType val)
    let suffIdx: Nat :=
      match suffIdx with
      | some i => i
      | none   => getLength type - 1
    let props := collectPropsInOrChain' suffIdx type
    let goal := createOrChain (permutateList props perm)
    let props := permutateList props perm.reverse
    go mvar props suffIdx val goal
where go : MVarId → List Expr → Nat → Expr → Expr → MetaM MVarId
      | mvar, [], _, acc, goal => mvar.withContext do
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal acc
        return mvar'
      | mvar, e::es, suffIdx, acc, goal =>
        mvar.withContext do
          let fname ← mkFreshId
          let type ← Meta.inferType acc
          let last: Bool ←
            match getIndex' e type suffIdx with
            | some i => pure $ i == suffIdx
            | none   => throwError "[permutateOr]: invalid permutation"
          let mvar' ← pullCore mvar e acc type suffIdx fname
          -- we need to update the new length of the suffix after pulling
          -- an element
          let length := getLength type suffIdx
          let currLastExpr := (getIthExpr? (length - 1) type).get!
          let suffIdx' :=
            if last then
              length - getLength currLastExpr
            else suffIdx
          mvar'.withContext do
            let ctx ← getLCtx
            let acc' := (ctx.findFromUserName? fname).get!.toExpr
            go mvar' es suffIdx' acc' goal

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? ("," term)? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat × Option Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) =>
    hs.toList.mapM stxToNat >>= λ li => return ⟨li, none⟩
  | `(tactic| permutateOr $_, [ $[$hs],* ], $i) =>
    hs.toList.mapM stxToNat >>= λ li =>
      elabTerm i none >>= λ i' =>
        return ⟨li, getNatLit? i'⟩
  | _ =>
    throwError "[permutateOr]: wrong usage"

@[tactic permutateOr] def evalPermutateOr : Tactic := fun stx =>
  withMainContext do
    let hyp ← elabTerm stx[1] none
    let ⟨hs, suffIdx⟩ ← parsePermuteOr stx
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← permutateOrMeta mvar hyp hs suffIdx fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ C ∨ D ∨ B ∨ E := by
  intro h
  permutateOr h, [0, 2, 3, 1, 4]

example : A ∨ (B ∨ C) ∨ (D ∨ E ∨ F) → (D ∨ E ∨ F) ∨ A ∨ (B ∨ C) := by
  intro h
  permutateOr h, [2, 0, 1], 2

end Smt.Reconstruction.Certifying
