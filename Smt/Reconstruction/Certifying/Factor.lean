import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Options
import Smt.Reconstruction.Certifying.Pull

open Lean Elab.Tactic Meta

def congDupOr (props : List Expr) (val : Expr) (i j : Nat) (last : Bool)
  : MetaM Expr :=
    match i with
    | 0     =>
      if last then
        mkAppM ``dupOr₂ #[val]
      else mkAppM ``dupOr #[val]
    | i + 1 => do
      let tailProps := createOrChain (props.drop (j + 1))
      withLocalDeclD (← mkFreshId) tailProps $ fun bv => do
        let r ← congDupOr props bv i (j + 1) last
        let lambda ← mkLambdaFVars #[bv] r
        mkAppM ``congOrLeft #[lambda, val]

-- i: the index fixed in the original list
-- j: the index of li.head! in the original list
def loop (mvar : MVarId) (i j n : Nat) (val pivot : Expr) (li : List Expr)
  (name : Name) : MetaM MVarId :=
  mvar.withContext do
    let type ← instantiateMVars $ ← inferType val
    match li with
    | []    =>
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type val
      return mvar'
    | e::es =>
      if e == pivot then
        let (mvar', step₁) ← 
          if j > i + 1 then
            let fname ← mkFreshId
            let mvar' ← pullToMiddleCore mvar (i + 1) j val type fname
            mvar'.withContext do
              let lctx ← getLCtx
              let answer := (lctx.findFromUserName? fname).get!.toExpr
              pure (mvar', answer)
          else pure (mvar, val)

          mvar'.withContext do
            let step₂ ← do
              let last := i + 1 == n - 1
              -- we are never trying to get the last prop
              -- so we don't need to use the function that
              -- produces the list considering the last suffix
              let type₁ ← inferType step₁
              let props := collectPropsInOrChain type₁
              congDupOr props step₁ i 0 last
            loop mvar' i j (n - 1) step₂ pivot es name
      else loop mvar i (j + 1) n val pivot es name

def factorCoreMeta (mvar : MVarId) (val type : Expr) (suffIdx : Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let initLength := getLength type
      let li := collectPropsInOrChain' suffIdx type
      let (answer, mvar') ← go mvar li (li.length - 1) li.length initLength val
      let goal: Expr := createOrChain li.eraseDups
      let (_, mvar'') ← MVarId.intro1P $ ← mvar'.assert name goal answer
      return mvar''
where
  go (mvar : MVarId) (li : List Expr) (i n initLength : Nat)
     (answer : Expr) : MetaM (Expr × MVarId) :=
       match i with
       | 0 => pure (answer, mvar)
       | i' + 1 =>
         let idx := n - i - 1
         match li.drop idx with
         | [] => pure (answer, mvar)
         | e::es => do
           let fname ← mkFreshId
           let mvar' ←
             loop mvar idx (idx + 1) li.length answer e es fname
           mvar'.withContext do
             let lctx ← getLCtx
             let answer' := (lctx.findFromUserName? fname).get!.toExpr
             let t ← instantiateMVars (← inferType answer')
             let newLength := getLength t
             let propsDropped := initLength - newLength
             let li' := collectPropsInOrChain' (suffIdx - propsDropped) t
             go mvar' li' i' n initLength answer'

syntax (name := factor) "factor" term ("," term)? : tactic

def parseFactor : Syntax → TacticM (Option Nat)
  | `(tactic| factor $_)     => pure none
  | `(tactic| factor $_, $i) => elabTerm i none >>= pure ∘ getNatLit?
  | _                        => throwError "[factor]: wrong usage"

@[tactic factor] def evalFactor : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let e ← elabTerm stx[1] none
    let type ← inferType e
    let lastSuffix := getLength type - 1
    let suffIdx :=
      match (← parseFactor stx) with
      | none => lastSuffix
      | some i => i
    let mvar ← getMainGoal
    let mvar' ← factorCoreMeta mvar e type suffIdx `pf
    replaceMainGoal [mvar']
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[factor] Time taken: {endTime - startTime}ms"

example : A ∨ B ∨ C ∨ B → A ∨ B ∨ C := by
  intro h
  factor h
  exact pf

example : A ∨ B ∨ B → A ∨ B := by
  intro h
  factor h
  exact pf

example : A ∨ A ∨ A ∨ A ∨ B ∨ A ∨ B ∨ A ∨ C ∨ B ∨ C ∨ B ∨ A → A ∨ B ∨ C :=
  by intro h
     factor h
     exact pf

example : (A ∨ B ∨ C) ∨ (A ∨ B ∨ C) → A ∨ B ∨ C := by
  intro h
  factor h, 1
  exact pf

example : (A ∨ B ∨ C) ∨ (E ∨ F) ∨ (A ∨ B ∨ C) ∨ (E ∨ F) → (A ∨ B ∨ C) ∨ (E ∨ F) := by
  intro h
  factor h, 3
  exact pf
