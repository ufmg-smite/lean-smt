/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Options
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List

namespace Smt.Reconstruction.Certifying.LiftOrNToImp

open Boolean Util

def groupPrefixLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| props, i_iter + 1, i,  e => do
  let rc ← groupPrefixLemmas' props i_iter i e
  mkAppOptM ``congOrLeft #[none, none, props.get! (i - i_iter - 1), rc]

def groupPrefixLemmasCore : Name → List Expr → Nat → MetaM (List Expr)
| nm, props, n =>
  let f := λ i: Nat => do
    let a₁ := props.get! i
    let a₂ := createOrChain $ List.take (n - i) (props.drop (i + 1))
    let a₃ := createOrChain $ props.drop (n + 1)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst nm) a₁) a₂) a₃
    groupPrefixLemmas' props i i appliedArgs
  List.mapM f (List.reverse (List.range n))

def groupPrefixLemmas := groupPrefixLemmasCore ``orAssocDir
def ungroupPrefixLemmas := fun props n => do
  pure $ List.reverse $ ← groupPrefixLemmasCore ``orAssocConv props n

def groupMiddleLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| sufProps, iter + 1, init, e => do
  let rc ← groupMiddleLemmas' sufProps iter init e
  mkAppOptM ``congOrLeft #[none, none, sufProps.get! (init - iter - 1), rc]

-- NOT a generalization of groupPrefixLemmas
-- exclusively used for pullMiddle (step₂)
def groupMiddleLemmas : List Expr → Nat → MetaM (List Expr)
| sufProps, groupSize =>
  let f := fun i: Nat => do
    let middleSize := groupSize + 1
    let a₁ := sufProps.get! i
    let a₂ := createOrChain $ List.take (groupSize - i - 1) (sufProps.drop (i + 1))
    let a₃ := sufProps.get! (middleSize - 1)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst ``orAssocDir) a₁) a₂) a₃
    groupMiddleLemmas' sufProps i i appliedArgs
  List.mapM f (List.reverse (List.range (groupSize - 1)))

def ungroupMiddleLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| props, iter + 1, init, e => do
  let rc ← ungroupMiddleLemmas' props iter init e
  let r := props.get! (init - iter - 1)
  mkAppOptM ``congOrLeft #[none, none, r, rc]

def ungroupMiddleLemmas : List Expr → Nat → Nat → MetaM (List Expr)
| props, groupStart, groupSize =>
  let f := fun i: Nat => do
    let a₁ := props.get! i
    let a₂ := createOrChain (subList (i + 1) (groupStart + groupSize - 1) props)
    let a₃ := createOrChain $ props.drop (groupStart + groupSize)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst ``orAssocConv) a₁) a₂) a₃
    ungroupMiddleLemmas' props i i appliedArgs
  -- [groupStart ..= groupStart + groupSize - 1]
  let is := List.drop groupStart (List.range (groupStart + groupSize - 1))
  List.mapM f is

def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (take n props)
          let right := createOrChain (drop n props)
          app (app (mkConst ``Or) left) right

def groupPrefixCore (mvar : MVarId) (val type : Expr) (prefLen : Nat)
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
          groupPrefixCore mvar val type prefLen fname1
        else pure mvar
      newMVar.withContext do
        let negArgs := collectOrNNegArgs type prefLen
        let deMorganArgs :=
          listExpr negArgs (sort Level.zero)
        let dmHyp :=
          mkApp (mkApp (mkConst ``deMorgan₂) deMorganArgs) (bvar 0)
        let lctx ← getLCtx
        let hyp    := (lctx.findFromUserName? fname1).get!.toExpr
        let props  := collectPropsInOrChain type
        let l      := createOrChain $ List.take prefLen props
        let r      := createOrChain $ List.drop prefLen props
        let answer :=
          mkApp (mkApp (mkApp (mkApp (mkConst ``orImplies₃) l) r) hyp) dmHyp
        let answer := mkLam (foldAndExpr negArgs) answer
        let (_, newMVar') ← MVarId.intro1P $ ← newMVar.assert name goal answer
        return newMVar'

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => withMainContext do
    let val ← elabTerm stx[1] none
    let prefLen ← stxToNat ⟨stx[3]⟩
    let mvar ← getMainGoal
    let mvar' ← liftOrNToImpCore mvar `pf val prefLen
    replaceMainGoal [mvar']

example : ¬ A ∨ ¬ B ∨ C ∨ D ∨ E → A ∧ B → C ∨ D ∨ E  := by
  intro h
  liftOrNToImp h, 2
  exact pf

end Smt.Reconstruction.Certifying.LiftOrNToImp
