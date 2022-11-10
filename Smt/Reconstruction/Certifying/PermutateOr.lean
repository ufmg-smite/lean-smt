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
      let type ← Meta.inferType hyp
      let hs ← parsePermuteOr stx
      let conclusion ← go hs.reverse type hyp stx[1]
      Tactic.closeMainGoal conclusion
    /- let endTime ← IO.monoMsNow -/
    /- logInfo m!"[permutateOr] Time taken: {endTime - startTime}ms" -/
where go : List Nat → Expr → Expr → Syntax → TacticM Expr
       | [], _, hyp, _ => return hyp
       | (i::is), type, hyp, stx => do
         let fname ← mkIdent <$> mkFreshId
         let ithExpr ←
           match getIthExpr? i type with
           | some e => pure e
           | none   => throwError "invalid permutation"
         let type ← instantiateMVars (← Meta.inferType hyp)
         pullCore ithExpr type stx fname
         withMainContext do
           let ctx ← getLCtx
           let hyp' := (ctx.findFromUserName? fname.getId).get!.toExpr
           go is type hyp' stx

