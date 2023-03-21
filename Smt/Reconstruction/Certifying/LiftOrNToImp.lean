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

def groupPrefixCore' (mvar : MVarId) (val type : Expr) (prefLen : Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let l := getLength type
      if prefLen > 0 && prefLen < l then
        let props := collectPropsInOrChain type
        let goal := getGroupOrPrefixGoal type prefLen
        let mut answer := val
        let lemmas ← groupPrefixLemmas props (prefLen - 1)
        for l in lemmas do
          answer := mkApp l answer
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal answer
        return mvar'
      else throwError
        "[groupPrefix]: prefix length must be > 0 and < size of or-chain"

syntax (name := testTac) "testTac" term : tactic
@[tactic testTac] def evalTestTac : Tactic := fun stx =>
  withMainContext do
    let e ← elabTerm stx[1] none
    let t ← inferType e
    let mvar ← getMainGoal
    let mvar' ← groupPrefixCore' mvar e t 3 `pf
    replaceMainGoal [mvar']

example : A ∨ B ∨ C ∨ D ∨ E → (A ∨ B ∨ C) ∨ D ∨ E := by
  intro h
  testTac h
  exact pf

def liftOrNToImpGoal (props : Expr) (prefLen : Nat) : Expr :=
  let propsList := collectPropsInOrChain props
  let conclusion := createOrChain $ List.drop prefLen propsList
  let premiss := foldAndExpr $ List.map notExpr $ List.take prefLen propsList
  mkForall' premiss conclusion

def liftOrNToImpCore (mvar : MVarId) (name : Name) (val : Expr)
  (prefLen : Nat) : MetaM MVarId :=
    mvar.withContext do
      /- let type ← (expandTypesInOrChain' mvar) $ ← inferType val -/
      let type ← inferType val
      let goal := liftOrNToImpGoal type prefLen
      let fname1 ← mkFreshId
      let newMVar ←
        if prefLen > 1 then
          groupPrefixCore' mvar val type prefLen fname1
        else pure mvar
      newMVar.withContext do
        let negArgs := collectOrNNegArgs type prefLen
        let deMorganArgs :=
          listExpr negArgs (sort Level.zero)
        let dmHyp :=
          mkApp (mkApp (mkConst `deMorgan₂) deMorganArgs) (bvar 0)
        let lctx ← getLCtx
        let hyp    := (lctx.findFromUserName? fname1).get!.toExpr
        let props  := collectPropsInOrChain type
        let l      := createOrChain $ List.take prefLen props
        let r      := createOrChain $ List.drop prefLen props
        let answer :=
          mkApp (mkApp (mkApp (mkApp (mkConst `orImplies₃) l) r) hyp) dmHyp
        let answer := mkLam (foldAndExpr negArgs) answer
        let (_, newMVar') ← MVarId.intro1P $ ← newMVar.assert name goal answer
        return newMVar'

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => withMainContext do
    let val ← elabTerm stx[1] none
    let prefLen ← stxToNat ⟨stx[3]⟩
    let mvar ← getMainGoal
    let mvar' ← liftOrNToImpCore mvar `blah val prefLen
    replaceMainGoal [mvar']

example : ¬ A ∨ ¬ B ∨ C ∨ D ∨ E → A ∧ B → C ∨ D ∨ E  := by
  intro h
  liftOrNToImp h, 2
  exact blah
  /- exact fun h₂ => orImplies₃ (orAssocDir h) (@deMorgan₂ [A, B] h₂) -/

