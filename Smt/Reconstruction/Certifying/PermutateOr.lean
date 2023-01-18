import Lean

import Smt.Reconstruction.Certifying.Pull
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) =>
    hs.toList.mapM stxToNat
  | _ =>
    throwError "[permutateOr]: wrong usage"

@[tactic permutateOr] def evalPermutateOr : Tactic :=
  fun stx => do
    /- let startTime ← IO.monoMsNow -/
    withMainContext do
      let hyp ← elabTerm stx[1] none
      let type ← instantiateMVars (← Meta.inferType hyp)
      let hs ← parsePermuteOr stx
      let s ← go hs.reverse type type stx[1]
      evalTactic (← `(tactic| exact $(⟨s⟩))) 
    /- let endTime ← IO.monoMsNow -/
    /- logInfo m!"[permutateOr] Time taken: {endTime - startTime}ms" -/
where go : List Nat → Expr → Expr → Syntax → TacticM Syntax
       | [], _, _, s => return s
       | (i::is), initialType, type, z => do
         let fname ← mkIdent <$> mkFreshId
         let ithExpr ←
           match getIthExpr? i initialType with
           | some e => pure e
           | none   => throwError "invalid permutation"
         pullCore ithExpr type z fname
         withMainContext do
           let ctx ← getLCtx
           let hyp' := (ctx.findFromUserName? fname.getId).get!.toExpr
           let type' ← instantiateMVars (← Meta.inferType hyp')
           go is initialType type' fname

