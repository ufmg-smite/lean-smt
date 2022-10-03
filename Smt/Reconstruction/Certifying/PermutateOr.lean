import Smt.Reconstruction.Certifying.Resolution

import Lean
open Lean
open Lean.Elab.Tactic Lean.Syntax Lean.Elab Lean.Expr
open Lean.Elab.Tactic

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) => hs.toList.mapM stxToNat
  | _                                      => throwError "ble"
where
  stxToNat (h : TSyntax `term) : TacticM Nat := do
    let expr ← elabTerm h.raw none
    match getNatLit? expr with
    | some i => pure i
    | none   => throwError "bla"

def getIthExpr : Nat → Expr → Option Expr
  | Nat.zero, app (app (const `Or ..) t₁) _ => some t₁
  | Nat.zero, t                             => some t -- last element in or chain
  | i + 1,    app (app (const `Or ..) _) t₂ => getIthExpr i t₂
  | _, _                                    => none

@[tactic permutateOr] def evalPermutateOr : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let type ← Meta.inferType hyp
    let hs ← parsePermuteOr stx
    let conclusion ← go hs.reverse type hyp
    Tactic.closeMainGoal conclusion
where go : List Nat → Expr → Expr → TacticM Expr
       | [], _, hyp => return hyp
       | (i::is), type, hyp => do
         let fname ← mkIdent <$> mkFreshId
         let fnameId := fname.getId
         let ithExpr ←
           match getIthExpr i type with
           | some e => pure e
           | none   => throwError "invalid permutation"
         logInfo m!"{ithExpr}"
         reorderCore ithExpr hyp fnameId
         withMainContext do
           let ctx ← getLCtx
           let hyp' := (ctx.findFromUserName? fnameId).get!.toExpr
           go is type hyp'


example : A ∨ B ∨ C ∨ D ∨ E → True := by
  intro h
  trivial
  /- permutateOr h, [2, 1, 3, 4, 0] -/
  /- trivial -/

