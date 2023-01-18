import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Pull

open Lean Elab.Tactic Meta

def congDupOr (i : Nat) (nm : Ident) (last : Bool) : TacticM Syntax :=
  match i with
  | 0 =>
    if last then `(dupOr₂ $nm)
    else `(dupOr $nm)
  | (i' + 1) => do
    let nm' := mkIdent (Name.mkSimple "w")
    let r ← congDupOr i' nm' last
    let r: Term := ⟨r⟩
    `(congOrLeft (fun $nm' => $r) $nm)

-- i: the index fixed in the original list
-- j: the index of li.head! in the original list
def loop (i j n : Nat) (pivot : Expr) (li : List Expr) (nm : Ident) : TacticM Ident :=
  match li with
  | [] => return nm
  | e::es =>
    if e == pivot then do
      -- step₁: move expr that is equal to the pivot to position i + 1
      let step₁ ←
        if j > i + 1 then
          let fname ← mkIdent <$> mkFreshId
          let e ← getTypeFromName nm.getId
          let t ← instantiateMVars e
          pullToMiddleCore (i + 1) j nm t fname
          pure fname
        else pure nm

      -- step₂: apply congOrLeft i times with dupOr
      let step₂: Ident ← do
        let last := i + 1 == n - 1
        let tactic ← congDupOr i step₁ last 
        let tactic := ⟨tactic⟩
        let fname ← mkIdent <$> mkFreshId
        evalTactic (← `(tactic| have $fname := $tactic))
        pure fname

      loop i j (n - 1) pivot es step₂
    else loop i (j + 1) n pivot es nm

def factorCore (type : Expr) (source : Ident) (suffixIdx : Nat) : TacticM Unit :=
  withMainContext do
    let initialLength := getLength type
    let mut li := collectPropsInOrChain' suffixIdx type
    let n := li.length
    let mut answer := source
    for i in List.range n do
      li := List.drop i li
      match li with
      | [] => break
      | e::es => do
        answer ← loop i (i + 1) (li.length + i) e es answer
        let e ← getTypeFromName answer.getId
        let t ← instantiateMVars e
        let newLength := getLength t
        let propsDropped := initialLength - newLength
        li := collectPropsInOrChain' (suffixIdx - propsDropped) t
    evalTactic (← `(tactic| exact $answer))

syntax (name := factor) "factor" term (",")? (term)? : tactic

def parseFactor : Syntax → TacticM (Option Nat)
  | `(tactic| factor $_)     => pure none
  | `(tactic| factor $_, $i) => elabTerm i none >>= pure ∘ getNatLit?
  | _                        => throwError "[factor]: wrong usage"

@[tactic factor] def evalFactor : Tactic := fun stx => do
  /- let startTime ← IO.monoMsNow -/
  withMainContext do
    let e ← elabTerm stx[1] none
    let type ← inferType e
    let lastSuffix := getLength type - 1
    let source := ⟨stx[1]⟩
    let sufIdx :=
      match (← parseFactor stx) with
      | none => lastSuffix
      | some i => i
    factorCore type source sufIdx
  /- let endTime ← IO.monoMsNow -/
  /- logInfo m!"[factor] Time taken: {endTime - startTime}ms" -/

example : A ∨ A ∨ A ∨ A ∨ B ∨ A ∨ B ∨ A ∨ C ∨ B ∨ C ∨ B ∨ A → A ∨ B ∨ C :=
  by intro h
     factor h

example : (A ∨ B ∨ C) ∨ (A ∨ B ∨ C) → A ∨ B ∨ C := by
  intro h
  factor h, 1

example : (A ∨ B ∨ C) ∨ (E ∨ F) ∨ (A ∨ B ∨ C) ∨ (E ∨ F) → (A ∨ B ∨ C) ∨ (E ∨ F) := by
  intro h
  factor h, 3
