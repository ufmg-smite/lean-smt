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

namespace Smt.Reconstruction.Certifying

def groupPrefixLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| props, i_iter + 1, i,  e => do
  let rc ← groupPrefixLemmas' props i_iter i e
  mkAppOptM ``congOrLeft #[none, none, props.get! (i - i_iter - 1), rc]

def groupPrefixLemmasCore : Name → List Expr → Nat → MetaM (List Expr)
| nm, props, n =>
  let f := fun i: Nat => do
    let a₁ := props.get! i
    let a₂ ← createOrChain $ List.take (n - i) (props.drop (i + 1))
    let a₃ ← createOrChain $ props.drop (n + 1)
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
    let a₂ ← createOrChain $ List.take (groupSize - i - 1) (sufProps.drop (i + 1))
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
    let a₂ ← createOrChain (subList (i + 1) (groupStart + groupSize - 1) props)
    let a₃ ← createOrChain $ props.drop (groupStart + groupSize)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst ``orAssocConv) a₁) a₂) a₃
    ungroupMiddleLemmas' props i i appliedArgs
  -- [groupStart ..= groupStart + groupSize - 1]
  let is := List.drop groupStart (List.range (groupStart + groupSize - 1))
  List.mapM f is

def getGroupOrPrefixGoal : Expr → Nat → MetaM Expr
| e, n => do
  let props ← collectPropsInOrChain e
  let left ← createOrChain (take n props)
  let right ← createOrChain (drop n props)
  pure $ app (app (mkConst ``Or) left) right

def groupPrefixCore (pf : Expr) (i : Nat) : MetaM Expr := do
  let clause ← inferType pf
  let props ← collectPropsInOrChain clause
  if i > 0 && i < List.length props then
    let lemmas ← groupPrefixLemmas props (i - 1)
    let answer :=
      List.foldl (fun acc l => Expr.app l acc) pf lemmas
    return answer
  else throwError
    "[groupPrefix]: prefix length must be > 0 and < size of or-chain"

syntax (name := groupClausePrefix) "groupClausePrefix" term "," term : tactic

@[tactic groupClausePrefix] def evalGroupClausePrefix : Tactic := fun stx =>
  withMainContext do
    let pf ← elabTerm stx[1] none
    let i ← stxToNat ⟨stx[3]⟩
    let answer ← groupPrefixCore pf i
    let mvar ← getMainGoal
    let type ← inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

def liftOrNToImpGoal (props : Expr) (prefLen : Nat) : MetaM Expr := do
  let propsList ← collectPropsInOrChain props
  let conclusion ← createOrChain $ List.drop prefLen propsList
  let premiss ← foldAndExpr $ List.map notExpr $ List.take prefLen propsList
  pure $ mkForall' premiss conclusion

def liftOrNToImpCore (pf : Expr) (prefLen : Nat) : MetaM Expr := do
    let clause ← inferType pf
    let newPf ←
      if prefLen > 1 then
        groupPrefixCore pf prefLen
      else pure pf
    let negArgs := collectOrNNegArgs clause prefLen
    let deMorganArgs :=
      listExpr negArgs (sort Level.zero)
    let dmHyp :=
      mkApp (mkApp (mkConst ``deMorgan₂) deMorganArgs) (bvar 0)
    let props  ← collectPropsInOrChain clause
    let l      ← createOrChain $ List.take prefLen props
    let r      ← createOrChain $ List.drop prefLen props
    let answer :=
      mkApp (mkApp (mkApp (mkApp (mkConst ``orImplies₃) l) r) newPf) dmHyp
    let answer := mkLam (← foldAndExpr negArgs) answer
    return answer

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => withMainContext do
    trace[smt.profile] m!"[liftOrNToImp] start time: {← IO.monoNanosNow}ns"
    let val ← elabTerm stx[1] none
    let prefLen ← stxToNat ⟨stx[3]⟩
    let answer ← liftOrNToImpCore val prefLen
    let mvar ← getMainGoal
    let type ← Meta.inferType answer
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile] m!"[liftOrNToImp] end time: {← IO.monoNanosNow}ns"
