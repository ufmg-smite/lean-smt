import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.LiftOrNToImp

namespace Smt.Reconstruction.Certifying

open Lean Elab Tactic

def applyList (l: List Term) (res: Term) : TacticM Term :=
  match l with
  | [] => return res
  | t::ts =>
    withMainContext do
      let res' := Syntax.mkApp t #[res]
      let fname ← mkIdent <$> mkFreshId
      evalTactic (← `(tactic| have $fname := $res'))
      applyList ts fname

def mkAppList : List Term → Ident → Syntax
| [], id => id
| t::ts, id =>
  let rest := mkAppList ts id
  let rest := ⟨rest⟩
  Syntax.mkApp t #[rest]

def congTactics (tactics : List Term) (i : Nat) (id : Ident) (last : Bool) : TacticM Syntax :=
  match i with
  | 0 => do
    if last then
      let innerProof := mkAppList tactics id
      let innerProof: Term := ⟨innerProof⟩
      `($innerProof)
    else
      let id' := mkIdent (Name.mkSimple "w")
      let innerProof := mkAppList tactics id'
      let innerProof: Term := ⟨innerProof⟩
      `(congOrRight (fun $id' => $innerProof) $id)
  | (i' + 1) => do
    let id' := mkIdent (Name.mkSimple "w")
    let r ← congTactics tactics i' id' last
    let r: Term := ⟨r⟩
    `(congOrLeft (fun $id' => $r) $id)

-- pull j-th term in the orchain to i-th position
-- (we start counting indices at 0)
-- TODO: clear intermediate steps
def pullToMiddleCore (i j : Nat) (hyp : Syntax) (type : Expr) (id : Ident)
  : TacticM Unit :=
  if i == j then do
    let hyp: Term := ⟨hyp⟩
    evalTactic (← `(tactic| have $id := $hyp))
  else withMainContext do
    let last := getLength type == j + 1
    let step₁: Ident ← 
      if last then pure ⟨hyp⟩
      else do
        let v := List.take (j - i) $ getCongAssoc j `orAssocDir
        let res: Term := ⟨hyp⟩
        let step₁: Term ← applyList v res
        let step₁: Ident := ⟨step₁⟩ 
        pure step₁ 

    let step₂: Ident ←
      if last then do
        let tactics := List.take (j - 1 - i) $ getCongAssoc (j - 1) `orAssocDir
        let step₂: Term ← applyList tactics step₁
        let step₂: Ident := ⟨step₂⟩
        pure step₂
      else do
        let tactics₂ := List.reverse $ getCongAssoc (j - i - 1) `orAssocDir
        let wrappedTactics₂: Syntax ← congTactics tactics₂ i step₁ last
        let wrappedTactics₂: Term := ⟨wrappedTactics₂⟩
        let fname₂ ← mkIdent <$> mkFreshId
        evalTactic (← `(tactic| have $fname₂ := $wrappedTactics₂))
        pure fname₂
    
    let orComm: Term := ⟨mkIdent `orComm⟩
    let wrappedTactics₃ ← congTactics [orComm] i step₂ last
    let wrappedTactics₃ := ⟨wrappedTactics₃⟩
    let step₃ ← mkIdent <$> mkFreshId
    evalTactic (← `(tactic| have $step₃ := $wrappedTactics₃))

    let step₄: Ident ←
      if last then pure step₃ 
      else do
        let u := List.reverse $ List.take (j - i) $ getCongAssoc j `orAssocConv
        let step₄: Term ← applyList u step₃
        let step₄: Ident := ⟨step₄⟩
        pure step₄

    evalTactic (← `(tactic| have $id := $step₄))

syntax (name := pullToMiddle) "pullToMiddle" term "," term "," term "," ident : tactic

@[tactic pullToMiddle] def evalPullToMiddle : Tactic := fun stx => withMainContext do
  let i ← stxToNat ⟨stx[1]⟩ 
  let j ← stxToNat ⟨stx[3]⟩
  let id: Ident := ⟨stx[7]⟩
  let e ← elabTerm stx[5] none
  let t ← instantiateMVars (← Meta.inferType e)
  pullToMiddleCore i j stx[5] t id

def pullIndex (index : Nat) (hypS : Syntax) (type : Expr) (id : Ident) : TacticM Unit :=
  pullToMiddleCore 0 index hypS type id

-- insert pivot in the first position of the or-chain
-- represented by hypS
def pullCore (pivot type : Expr) (hypS : Syntax) (id : Ident)
  (sufIdx : Option Nat := none) : TacticM Unit :=
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
          evalTactic (← `(tactic| have $id := $(⟨hypS⟩)))
        else
          let ctx ← getLCtx
          let hyp := (ctx.findFromUserName? hypS.getId).get!.toExpr
          let fname ← mkFreshId
          groupOrPrefixCore hyp type sufIdx fname
          evalTactic (← `(tactic| have $id := orComm $(mkIdent fname)))
      else
        pullIndex i hypS type id
  | none   => throwError "[Pull]: couldn't find pivot"

syntax (name := pull) "pull" term "," term "," ident : tactic

@[tactic pull] def evalPullCore : Tactic := fun stx => withMainContext do
  let e ← elabTerm stx[1] none
  let t ← instantiateMVars (← Meta.inferType e)
  let e₂ ← elabTerm stx[3] none
  pullCore e₂ t stx[1] ⟨stx[5]⟩

/- example : A ∨ B ∨ C ∨ D ∨ E → E ∨ A ∨ B ∨ C ∨ D := by -/
/-   intro h -/
/-   pull h, E, h₂ -/

end Smt.Reconstruction.Certifying
