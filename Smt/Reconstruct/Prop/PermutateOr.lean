/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruct.Prop.Pull
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Prop

open Lean Elab Tactic

def permutateOrMeta (val : Expr) (perm : List Nat)
    (suffIdx : Option Nat) : MetaM Expr := do
  let type ← instantiateMVars (← Meta.inferType val)
  let suffIdx: Nat ←
    match suffIdx with
    | some i => pure i
    | none   => pure $ (← getLength type) - 1
  let props ← collectPropsInOrChain' suffIdx type
  let props := permutateList props perm.reverse
  go props suffIdx val
where go : List Expr → Nat → Expr → MetaM Expr
      | [], _, acc => return acc
      | e::es, suffIdx, acc => do
          let type ← Meta.inferType acc
          let pulled ← pullCore e acc type suffIdx
          go es suffIdx pulled

def traceReorder (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def reorder (mv : MVarId) (e : Expr) (is : Array Nat) (i : Option Nat) : MetaM Unit := withTraceNode `smt.reconstruct.reorder traceReorder do
  let answer ← permutateOrMeta e is.toList i
  mv.assign answer

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? ("," term)? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat × Option Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) =>
    hs.toList.mapM stxToNat >>= λ li => return ⟨li, none⟩
  | `(tactic| permutateOr $_, [ $[$hs],* ], $i) =>
    hs.toList.mapM stxToNat >>= λ li =>
      elabTerm i none >>= λ i' =>
        return ⟨li, getNatLit? i'⟩
  | _ => throwError "[permutateOr]: wrong usage"

@[tactic permutateOr] def evalPermutateOr : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[permutateOr] start time: {← IO.monoNanosNow}ns"
    let hyp ← elabTerm stx[1] none
    let ⟨hs, suffIdx⟩ ← parsePermuteOr stx
    let answer ← permutateOrMeta hyp hs suffIdx
    let mvar ← getMainGoal
    let type ← instantiateMVars (← Meta.inferType answer)
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[permutateOr] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruct.Prop
