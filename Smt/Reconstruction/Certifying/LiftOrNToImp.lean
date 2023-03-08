import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Options
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (take n props)
          let right := createOrChain (drop n props)
          app (app (mkConst `Or) left) right

def implicitArgs : List Expr → Nat → Nat → Expr × Expr × Expr
| props, i, j  =>
  let third := createOrChain $ List.drop j props
  let second := createOrChain $ List.take (j - i) (List.drop i props)
  let first := List.get! props (i - 1)
  (first, second, third)

def go' : List Expr → Nat → Expr → MetaM Expr
| _, 0, e => pure e
| props, i + 1, e => do
  let rc ← go' props i e
  mkAppOptM `congOrLeft #[none, none, props.get! i ,rc]

def go : List Expr → Nat → MetaM (List Expr)
| props, n =>
  let f := λ i: Nat =>
    let (a₁, a₂, a₃) := implicitArgs props (i + 1) (n + 1)
    go' props i (mkApp (mkApp (mkApp (mkConst `orAssocDir) a₁) a₂) a₃)
  List.mapM f (List.reverse (List.range n))

def groupOrPrefixCore' (mvar : MVarId) (val type : Expr) (prefLen : Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let l := getLength type
      if prefLen > 0 && prefLen < l then
        let props := collectPropsInOrChain type
        let goal := getGroupOrPrefixGoal type prefLen
        let mut answer := val
        for e in ← go props (prefLen - 1) do
          answer := mkApp e answer
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal answer
        return mvar'
      else throwError
        "[groupOrPrefix]: prefix length must be > 0 and < size of or-chain"

syntax (name := testTac) "testTac" term : tactic
@[tactic testTac] def evalTestTac : Tactic := fun stx =>
  withMainContext do
    let e ← elabTerm stx[1] none
    let t ← inferType e
    let mvar ← getMainGoal
    let mvar' ← groupOrPrefixCore' mvar e t 3 `bleh
    replaceMainGoal [mvar']

example : A ∨ B ∨ C ∨ D ∨ E → (A ∨ B ∨ C) ∨ D ∨ E := by
  intro h
  testTac h
  exact bleh

-- groups the given prefix of the given hypothesis (assuming it is an
-- or-chain) and adds this as a new hypothesis with the given name
def groupOrPrefixCore (hyp type : Expr) (prefLen : Nat) (name : Name)
  : TacticM Unit := withMainContext do
    let l := getLength type
    if prefLen > 0 && prefLen < l then
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
           "[groupOrPrefix]: prefix length must be > 0 and < size of or-chain"

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
      let expandedType ← expandTypesInOrChain type
      let li :=
        listExpr (collectOrNNegArgs expandedType prefLen) (sort Level.zero)
      withMainContext do
        let ctx ← getLCtx
        let hyp2 := (ctx.findFromUserName? fname2.getId).get!.toExpr
        Tactic.closeMainGoal $ mkApp (mkApp (mkConst `deMorgan₂) li) hyp2
    let endTime ← IO.monoMsNow
    trace[smt.profile] m!"[liftOrNToImp]: Time taken: {endTime - startTime}ms"

