import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.LiftOrNToImp

open Lean Elab Tactic Meta

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
          mkAppM `congOrRight #[lambda, val]
    | i_iter' + 1 =>
      let fname ← mkFreshId
      let pref := subList (i - i_iter + 1) (i - 1) props
      /- let mid := subList i (j - 1) props -/
      /- let mid_right := props.get! j -/
      let suff := subList (j + 1) props.length props
      let mut t := mid -- createOrChain [createOrChain mid, mid_right]
      if not suff.isEmpty then
        t := createOrChain [t, createOrChain suff]
      if not pref.isEmpty then
        let l' := collectPropsInOrChain t
        t := createOrChain (pref ++ l')
      withLocalDeclD fname t $ fun bv => do
        let rc ← congLemmas lemmas props i_iter' i j bv mid last
        let lambda ← mkLambdaFVars #[bv] rc
        mkAppM `congOrLeft #[lambda, val]

-- pull j-th term in the orchain to i-th position
-- (we start counting indices at 0)
def pullToMiddleCore (mvar: MVarId) (i j : Nat) (val type : Expr) (name : Name)
  : MetaM MVarId := mvar.withContext do
  if i == j then
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name val type  
    return mvar'
  else
    let last := getLength type == j + 1
    let props := collectPropsInOrChain type
    let mid := List.take (j - i + 1) (List.drop i props)

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
      let mid := createOrChain (subList i j props)
      congLemmas lemmas props i i j step₁ mid last

    /- -- step₃: apply commutativity on middle -/
    /- -- example: A ∨ ((B ∨ C) ∨ D) ∨ E -/
    /- --       -> A ∨ (D ∨ B ∨ C) ∨ E -/
    let midPref := List.dropLast mid
    let midSuff := List.getLast! mid
    let comm :=
      mkApp (mkApp (mkConst `orComm) (createOrChain midPref)) midSuff
    let mid := createOrChain [createOrChain midPref, midSuff]
    let step₃ ← congLemmas [comm] props i i j step₂ mid last
  
    /- -- step₄: ungroup middle -/
    /- -- example: A ∨ (D ∨ B ∨ C) ∨ E -/
    /- --       -> A ∨ D ∨ B ∨ C ∨ E -/
    let goalList := pull! i j props
    let goal := createOrChain goalList
    let step₄ ←
      if last then pure step₃
      else do
        let lemmas ← ungroupMiddleLemmas goalList i (j - i + 1)
        pure $ mkAppList step₃ lemmas
    let (_, mvar₄) ← MVarId.intro1P $ ← mvar.assert name goal step₄
    return mvar₄

syntax (name := pullToMiddle) "pullToMiddle" term "," term "," term "," ident : tactic

@[tactic pullToMiddle] def evalPullToMiddle : Tactic := fun stx => withMainContext do
  let i ← stxToNat ⟨stx[1]⟩ 
  let j ← stxToNat ⟨stx[3]⟩
  let id: Ident := ⟨stx[7]⟩
  let e ← elabTerm stx[5] none
  let t ← instantiateMVars (← inferType e)
  let mvar ← getMainGoal
  let mvar' ← pullToMiddleCore mvar i j e t id.getId
  replaceMainGoal [mvar']

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G → A ∨ B ∨ C ∨ F ∨ D ∨ E ∨ G := by
  intro h
  pullToMiddle 3, 5, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I ∨ J →
          A ∨ J ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I := by
  intro h
  pullToMiddle 1, 9, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ C ∨ G ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 3, 6, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ E ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 2, 4, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → E ∨ A ∨ B ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 0, 4, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ G ∨ B ∨ C ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 1, 6, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F → A ∨ B ∨ C ∨ F ∨ D ∨ E := by
  intro h
  pullToMiddle 3, 5, h, h₂
  exact h₂

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ E ∨ B ∨ C ∨ D := by
  intro h
  pullToMiddle 1, 4, h, h₂
  exact h₂

def pullIndex (mvar: MVarId) (index : Nat) (val type : Expr)
  (name : Name) : MetaM MVarId :=
    pullToMiddleCore mvar 0 index val type name

def pullCore' (mvar: MVarId) (pivot val type : Expr) (sufIdx : Option Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let lastSuffix := getLength type - 1
      let sufIdx :=
        match sufIdx with
        | some i => i
        | none   => lastSuffix
      let li := collectPropsInOrChain' sufIdx type
      match getIndexList pivot li with
      | some i =>
        if i == sufIdx && sufIdx != lastSuffix then do
          if i == 0 then
            return mvar
          else
            let fname ← mkFreshId
            let mvar' ← groupPrefixCore' mvar val type sufIdx fname
            mvar'.withContext do
              let lctx ← getLCtx
              let groupped := (lctx.findFromUserName? fname).get!.toExpr
              let answer: Expr ←
                mkAppM `orComm #[groupped]
              let requiredType ← inferType answer
              let (_, mvar'') ← MVarId.intro1P $
                ← mvar'.assert name requiredType answer
              return mvar''
        else throwError "unimplemented"
/-         pullIndex i hypS type id -/
      | none   => throwError "[Pull]: couldn't find pivot"

syntax (name := pull) "pull" term "," term "," ident ("," term)? : tactic

def parsePull : Syntax → TacticM (Option Nat)
  | `(tactic| pull $_, $_, $_, $i) =>
    elabTerm i none >>= pure ∘ getNatLit?
  | _                      => pure none

@[tactic pull] def evalPullCore : Tactic := fun stx => withMainContext do
  let e ← elabTerm stx[1] none
  let t ← instantiateMVars (← inferType e)
  let e₂ ← elabTerm stx[3] none
  let i ← parsePull stx
  let mvar ← getMainGoal
  let mvar' ← pullCore' mvar e₂ e t i `blah
  replaceMainGoal [mvar']

example : A ∨ B ∨ C ∨ D ∨ E → (D ∨ E) ∨ A ∨ B ∨ C := by
  intro h
  pull h, (D ∨ E), h₂, 3
  exact blah

