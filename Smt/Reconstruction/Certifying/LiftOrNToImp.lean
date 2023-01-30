import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (take n props)
          let right := createOrChain (drop n props)
          app (app (mkConst `Or) left) right

-- groups the given prefix of the given hypothesis (assuming it is an
-- or-chain) and adds this as a new hypothesis with the given name
def groupOrPrefixCore (hyp type : Expr) (prefLen : Nat) (name : Name)
  : TacticM Unit := withMainContext do
    let l := getLength type
    if prefLen > 1 && prefLen < l then
      let mvarId ← getMainGoal
      MVarId.withContext mvarId do
        let newTerm := getGroupOrPrefixGoal type prefLen
        let p ← Meta.mkFreshExprMVar newTerm MetavarKind.syntheticOpaque name
        let (_, mvarIdNew) ← MVarId.intro1P $ ← MVarId.assert mvarId name newTerm p
        replaceMainGoal [p.mvarId!, mvarIdNew]
      for t in reverse (getCongAssoc (prefLen - 1) `orAssocDir) do
        evalTactic  (← `(tactic| apply $t))
      Tactic.closeMainGoal hyp
    else throwError
           "[groupOrPrefix]: prefix length must be > 1 and < size of or-chain"

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => do
    let startTime ← IO.monoMsNow
    withMainContext do
      let prefLen ← stxToNat ⟨stx[3]⟩
      let fname1 ← mkFreshId
      let fident1 := mkIdent fname1
      let hyp ← Tactic.elabTerm stx[1] none
      let type ← inferType hyp
      if prefLen > 1 then
        groupOrPrefixCore hyp type prefLen fname1
      else
        evalTactic (← `(tactic| have $fident1 := $(⟨stx[1]⟩)))
      let fname2 ← mkIdent <$> mkFreshId
      evalTactic (← `(tactic| intros $fname2))
      evalTactic (← `(tactic| apply orImplies₃ $fident1))
      let li := listExpr (collectOrNNegArgs type prefLen) (Expr.sort Level.zero)
      withMainContext do
        let ctx ← getLCtx
        let hyp2 := (ctx.findFromUserName? fname2.getId).get!.toExpr
        Tactic.closeMainGoal $ mkApp (mkApp (mkConst `deMorgan₂) li) hyp2
    let endTime ← IO.monoMsNow
    logInfo m!"[liftOrNToImp] Time taken: {endTime - startTime}ms"

example {A B C : Prop} : ¬ A ∨ ¬ B ∨ ¬ C → A → ¬ B ∨ ¬ C := by
  intros h₁
  liftOrNToImp h₁, 1
