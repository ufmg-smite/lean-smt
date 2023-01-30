import Lean

import Smt.Reconstruction.Certifying.Pull
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic

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

@[tactic permutateOr] def evalPermutateOr : Tactic :=
  fun stx => do
    let startTime ← IO.monoMsNow
    withMainContext do
      let hyp ← elabTerm stx[1] none
      let type ← instantiateMVars (← Meta.inferType hyp)
      let ⟨hs, suffIdx⟩ ← parsePermuteOr stx
      let suffIdx: Nat :=
        match suffIdx with
        | some i => i
        | none   => getLength type - 1
      let props := collectPropsInOrChain' suffIdx type
      let props' := permutateList props hs.reverse
      let s ← go props' suffIdx type stx[1]
      evalTactic (← `(tactic| exact $(⟨s⟩))) 
    let endTime ← IO.monoMsNow
    logInfo m!"[permutateOr] Time taken: {endTime - startTime}ms"
where go : List Expr → Nat → Expr → Syntax → TacticM Syntax
       | [], _, _, stx => return stx
       | (e::es), suffIdx, type, stx => do
         let fname ← mkIdent <$> mkFreshId
         let last: Bool :=
           match getIndex e type with
           | some i => i == suffIdx
           | none   => panic! "[permutateOr]: invalid permutation"
         pullCore e type stx fname suffIdx
         -- we need to update the new length of the suffix after pulling
         -- an element
         let length := getLength type suffIdx
         let currLastExpr := (getIthExpr? (length - 1) type).get!
         let suffIdx' :=
           if last then
             length - getLength currLastExpr
           else suffIdx
         withMainContext do
           let ctx ← getLCtx
           let hyp' := (ctx.findFromUserName? fname.getId).get!.toExpr
           let type' ← instantiateMVars (← Meta.inferType hyp')
           go es suffIdx' type' fname

