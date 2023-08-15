/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.LiftOrNToImp
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta

namespace Smt.Reconstruction.Certifying

def mkAppList : Expr → List Expr → Expr :=
  fun e l => List.foldr mkApp e l.reverse

def mkAppListM : Expr → List Expr → MetaM Expr
| e, [] => pure e
| e, f::fs => do
  let rc ← mkAppListM e fs
  mkAppM' f #[rc]

def congLemmas (lemmas props : List Expr) (i_iter i j : Nat)
   (val : Expr) (mid : Expr) (last : Bool) : MetaM Expr := do
    match i_iter with
    | 0      =>
      if last then pure $ mkAppList val lemmas
      else
        let fname ← mkFreshId
        withLocalDeclD fname mid $ fun bv => do
          let body := mkAppList bv lemmas
          let lambda ← mkLambdaFVars #[bv] body
          mkAppM ``congOrRight #[lambda, val]
    | i_iter' + 1 =>
      let fname ← mkFreshId
      let pref := subList (i - i_iter + 1) (i - 1) props
      let suff := subList (j + 1) props.length props
      let mut t := mid
      if not suff.isEmpty then
        t ← createOrChain [t, ← createOrChain suff]
      if not pref.isEmpty then
        let l' ← collectPropsInOrChain t
        t ← createOrChain (pref ++ l')
      withLocalDeclD fname t $ fun bv => do
        let rc ← congLemmas lemmas props i_iter' i j bv mid last
        let lambda ← mkLambdaFVars #[bv] rc
        mkAppM ``congOrLeft #[lambda, val]

-- pull j-th term in the orchain to i-th position
-- (we start counting indices at 0)
def pullToMiddleCore  (i j suffIdx : Nat) (val type : Expr)
  : MetaM Expr := do
  if i == j then return val
  else
    let last := suffIdx == j
    let props ← collectPropsInOrChain' suffIdx type
    let mid := List.take (j + 1 - i) (List.drop i props)
    let midExpr ← createOrChain mid

    -- step₁: group with parenthesis props in the range [i, j]
    -- example: A ∨ B ∨ C ∨ D ∨ E with (2, 4)
    --       -> A ∨ (B ∨ C ∨ D) ∨ E
    let step₁ ←
      if last then pure val
      else do
        let lemmas := List.take (j - i) $ ← groupPrefixLemmas props j
        pure (mkAppList val lemmas)
/- -- step₂: group prefix of middle -/
    /- -- example: A ∨ (B ∨ C ∨ D) ∨ E -/
    /- --       -> A ∨ ((B ∨ C) ∨ D) ∨ E -/
    let step₂: Expr ← do
      let lemmas ← groupMiddleLemmas (props.drop i) (j - i)
      congLemmas lemmas props i i j step₁ midExpr last

    /- -- step₃: apply commutativity on middle -/
    /- -- example: A ∨ ((B ∨ C) ∨ D) ∨ E -/
    /- --       -> A ∨ (D ∨ B ∨ C) ∨ E -/
    let midPref := List.dropLast mid
    let midSuff := List.getLast! mid
    let comm :=
      mkApp (mkApp (mkConst ``orComm) (← createOrChain midPref)) midSuff
    let mid' ← createOrChain [← createOrChain midPref, midSuff]
    let step₃ ← congLemmas [comm] props i i j step₂ mid' last
  
    /- -- step₄: ungroup middle -/
    /- -- example: A ∨ (D ∨ B ∨ C) ∨ E -/
    /- --       -> A ∨ D ∨ B ∨ C ∨ E -/
    let goalList := pull! i j props
    let step₄ ←
      if last then pure step₃
      else do
        let lemmas ← ungroupMiddleLemmas goalList i (j - i + 1)
        pure $ mkAppList step₃ lemmas
    return step₄

syntax (name := pullToMiddle) "pullToMiddle" term "," term "," term ("," term)? : tactic

def parsePullToMiddle : Syntax → TacticM (Option Nat)
  | `(tactic| pullToMiddle $_, $_, $_, $i) =>
    elabTerm i none >>= pure ∘ getNatLit?
  | _                      => pure none

@[tactic pullToMiddle] def evalPullToMiddle : Tactic := fun stx => withMainContext do
  let i ← stxToNat ⟨stx[1]⟩ 
  let j ← stxToNat ⟨stx[3]⟩
  let e ← elabTerm stx[5] none
  let t ← instantiateMVars (← inferType e)
  let suffIdx ← parsePullToMiddle stx
  let suffIdx ←
    match suffIdx with
    | some i => pure i
    | none   => pure ((← getLength t) - 1) 
  let answer ← pullToMiddleCore i j suffIdx e t
  closeMainGoal answer

def pullIndex (index : Nat) (suffIdx : Option Nat) (val type : Expr) :
    MetaM Expr := do
  let suffIdx ←
    match suffIdx with
    | some i => pure i
    | none   => getLength type
  pullToMiddleCore 0 index suffIdx val type

def pullCore (pivot val type : Expr) (suffIdx : Option Nat) :
    MetaM Expr := do
  let lastSuffix := (← getLength type) - 1
  let suffIdx :=
    match suffIdx with
    | some i => i
    | none   => lastSuffix
  let li ← collectPropsInOrChain' suffIdx type
  match findIndex? li pivot with
  | some i =>
    if i == suffIdx && suffIdx != lastSuffix then
      if i == 0 then return val
      else
        let groupped ← groupPrefixCore val suffIdx
        let answer: Expr ← mkAppM ``orComm #[groupped]
        return answer
    else pullIndex i suffIdx val type
  | none   => throwError "[Pull]: couldn't find pivot"

syntax (name := pull) "pull" term "," term ("," term)? : tactic

def parsePull : Syntax → TacticM (Option Nat)
  | `(tactic| pull $_, $_, $i) =>
    elabTerm i none >>= pure ∘ getNatLit?
  | _                      => pure none

@[tactic pull] def evalPullCore : Tactic := fun stx => withMainContext do
  let hyp ← elabTerm stx[1] none
  let t ← instantiateMVars (← inferType hyp)
  let pivot ← elabTerm stx[3] none
  let i ← parsePull stx
  let answer ← pullCore pivot hyp t i
  closeMainGoal answer

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ B ∨ D ∨ C ∨ E := by
  intro h
  pullToMiddle 2, 3, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G → A ∨ B ∨ C ∨ F ∨ D ∨ E ∨ G := by
  intro h
  pullToMiddle 3, 5, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I ∨ J →
          A ∨ J ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I := by
  intro h
  pullToMiddle 1, 9, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ C ∨ G ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 3, 6, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ E ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 2, 4, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → E ∨ A ∨ B ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 0, 4, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ G ∨ B ∨ C ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 1, 6, h

example : A ∨ B ∨ C ∨ D ∨ E ∨ F → A ∨ B ∨ C ∨ F ∨ D ∨ E := by
  intro h
  pullToMiddle 3, 5, h

example : A ∨ B ∨ C ∨ D → A ∨ D ∨ B ∨ C := by
  intro h
  pullToMiddle 1, 3, h

example : A ∨ B ∨ C ∨ D ∨ E → (D ∨ E) ∨ A ∨ B ∨ C := by
  intro h
  pull h, (D ∨ E),  3

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → F ∨ A ∨ B ∨ C ∨ D ∨ E ∨ G ∨ H := by
  intro h
  pull h, F

end Smt.Reconstruction.Certifying
