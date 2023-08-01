/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Options

open Lean Elab.Tactic Meta Expr Syntax
open Nat List Classical

namespace Smt.Reconstruction.Certifying

/- abbrev Implies (p q : Prop) := p → q -/

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases Classical.em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem equivElim1 : ∀ {P Q : Prop}, Eq P Q → ¬ P ∨ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inr q
  | inr nq => exact Or.inl nq

theorem equivElim2 : ∀ {P Q : Prop}, Eq P Q → P ∨ ¬ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inl q
  | inr nq => exact Or.inr nq

theorem notEquivElim1 : ∀ {P Q : Prop}, ¬ (Eq P Q) → P ∨ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inl p, _ => Or.inl p
  | _, Or.inl q => Or.inr q
  | Or.inr np, Or.inr nq =>
    absurd (propext (Iff.intro (λ p => absurd p np) (λ q => absurd q nq))) h

theorem notEquivElim2 : ∀ {P Q : Prop}, ¬ (Eq P Q) → ¬ P ∨ ¬ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inr np, _ => Or.inl np
  | _, Or.inr nq => Or.inr nq
  | Or.inl p, Or.inl q =>
    absurd (propext (Iff.intro (λ _ => q) (λ _ => p))) h

theorem iteElim1 : ∀ {c a b : Prop}, ite c a b → ¬ c ∨ a := by
  intros c a b h
  cases Classical.em c with
  | inl hc => have r: ite c a b = a := if_pos hc
              rewrite [r] at h
              exact Or.inr h
  | inr hnc => exact Or.inl hnc

theorem iteElim2 : ∀ {c a b : Prop}, ite c a b → c ∨ b := by
  intros c a b h
  cases Classical.em c with
  | inl hc => exact Or.inl hc
  | inr hnc => have r: ite c a b = b := if_neg hnc
               rewrite [r] at h
               exact Or.inr h

theorem notIteElim1 : ∀ {c a b : Prop}, ¬ ite c a b → ¬ c ∨ ¬ a := by
  intros c a b h
  cases Classical.em c with
  | inl hc  => have r : ite c a b = a := if_pos hc
               rewrite [r] at h
               exact Or.inr h
  | inr hnc => exact Or.inl hnc

theorem notIteElim2 : ∀ {c a b : Prop}, ¬ ite c a b → c ∨ ¬ b := by
  intros c a b h
  cases Classical.em c with
  | inl hc => exact Or.inl hc
  | inr hnc => have r : ite c a b = b := if_neg hnc
               rewrite [r] at h
               exact Or.inr h

theorem contradiction : ∀ {P : Prop}, P → ¬ P → False := λ p np => np p

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {P Q R : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem orImplies₂ : ∀ {p q : Prop}, (¬ p) ∨ q → p → q := by
  intros P Q h p
  cases h with
  | inl np => exact False.elim (np p)
  | inr q  => exact q

theorem orImplies₃ : ∀ {p q : Prop}, p ∨ q → ¬ p → q := by
  intros P Q h np
  cases h with
  | inl p => exact False.elim (np p)
  | inr q => exact q

theorem scope : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q := scope

theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _          => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq

theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _   => False.elim (np pp)
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp)
                                    | Or.inr pq => False.elim (npq pq)

theorem deMorganSmall₃ : ∀ {p q : Prop}, ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  by intros p q h
     match Classical.em p, Classical.em q with
     | Or.inl hp, Or.inl hq  => exact False.elim (h (And.intro hp hq))
     | _,         Or.inr hnq => exact Or.inr hnq
     | Or.inr hnp, _        => exact Or.inl hnp

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem notNotIntro : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p

theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notList l) → andN l :=
  by intros l h
     exact match l with
     | []   => True.intro
     | [t]  => by simp [andN]
                  simp [notList, orN, map] at h
                  cases Classical.em t with
                  | inl tt  => exact tt
                  | inr ntt => exact False.elim (ntt h)
     | h₁::h₂::t => by simp [orN, notList, map] at h
                       have ⟨ t₁, t₂ ⟩ := deMorganSmall h
                       simp [orN] at t₂
                       have ih := @deMorgan (h₂::t) t₂
                       simp [andN]
                       have t₁' := notNotElim t₁
                       exact ⟨ t₁', ih ⟩

theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notList l) :=
  by intros l h
     exact match l with
     | [] => by simp [orN, notList]
     | [t] => by simp [orN, notList]; simp [andN] at h; exact h
     | h₁::h₂::t => by simp [orN, notList, map]
                       simp [andN] at h
                       apply deMorganSmall₂
                       have nnh₁ := notNotIntro (And.left h)
                       have ih := @deMorgan₂ (h₂::t) (And.right h)
                       exact ⟨nnh₁, ih⟩

theorem deMorgan₃ : ∀ {l : List Prop}, ¬ orN l → andN (notList l) :=
  by intros l h
     exact match l with
     | [] => True.intro
     | [t] => by simp [andN, notList, map]
                 simp [orN, Not] at h
                 exact h
     | h₁::h₂::t => by simp [orN, Not] at h
                       have ⟨t₁, t₂⟩ := deMorganSmall h
                       simp [orN, Not] at t₂
                       simp [andN, notList, map]
                       have ih := @deMorgan₃ (h₂::t) t₂
                       exact ⟨t₁, ih⟩

theorem cnfAndNeg : ∀ (l : List Prop), andN l ∨ orN (notList l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h

theorem cnfAndPos : ∀ (l : List Prop) (i : Nat), ¬ (andN l) ∨ List.getD l i True :=
  by intros l i
     apply orImplies
     intro h
     have h' := notNotElim h
     match l with
     | [] => exact True.intro
     | [p] =>
       match i with
       | 0 => exact h'
       | _ + 1 => exact True.intro
     | p₁::p₂::ps =>
       match i with
       | 0 => exact And.left h'
       | i' + 1 =>
         have IH :=  cnfAndPos (p₂::ps) i'
         exact orImplies₂ IH (And.right h')

theorem cnfOrNeg : ∀ (l : List Prop) (i : Nat), orN l ∨ ¬ List.getD l i False := by
  intros l i
  apply orImplies
  intros orNl p
  have andNotl := @deMorgan₃ l orNl
  match l with
  | [] => exact False.elim p
  | [h] =>
    match i with
    | 0 => exact absurd p orNl
    | _ + 1 => exact False.elim p
  | h₁::h₂::hs =>
    match i with
    | 0 => have ⟨nh₁p, _⟩ := andNotl
           exact absurd p nh₁p
    | i' + 1 =>
      have IH := cnfOrNeg (h₂::hs) i'
      have orNTail := orImplies₂ (orComm IH) p
      have ⟨_, notOrNTail⟩ := deMorganSmall orNl
      exact absurd orNTail notOrNTail

theorem cnfOrPos : ∀ (l : List Prop), ¬ orN l ∨ orN l := λ l => orComm (Classical.em (orN l))

theorem cnfImpliesPos : ∀ {p q : Prop}, ¬ (p → q) ∨ ¬ p ∨ q := by
  intros p q
  match Classical.em p, Classical.em q with
  | _,         Or.inl hq  => exact Or.inr (Or.inr hq)
  | Or.inl hp, Or.inr hnq => apply Or.inl
                             intro f
                             exact absurd (f hp) hnq
  | Or.inr hnp, _         => exact Or.inr (Or.inl hnp)

theorem cnfImpliesNeg1 : ∀ {p q : Prop}, (p → q) ∨ p := by
  intros p q
  apply orComm
  apply orImplies
  exact flip absurd

theorem cnfImpliesNeg2 : ∀ {p q : Prop}, (p → q) ∨ ¬ q := by
  intros p q
  apply orComm
  apply orImplies
  intros hnnq _
  exact notNotElim hnnq

theorem cnfEquivPos1 : ∀ {p q : Prop}, ¬ (Eq p q) ∨ ¬ p ∨ q := by
  intros _ _
  apply orImplies
  exact equivElim1 ∘ notNotElim

theorem cnfEquivPos2 : ∀ {p q : Prop}, ¬ (Eq p q) ∨ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact equivElim2 ∘ notNotElim

theorem cnfEquivNeg1 : ∀ {p q : Prop}, Eq p q ∨ p ∨ q := by
  intros _ _
  apply orImplies
  exact notEquivElim1

theorem cnfEquivNeg2 : ∀ {p q : Prop}, Eq p q ∨ ¬ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact notEquivElim2

theorem cnfItePos1 : ∀ {c a b : Prop}, ¬ (ite c a b) ∨ ¬ c ∨ a := by
  intros c a b
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match Classical.em c with
  | Or.inl hc  => have r: (if c then a else b) = a := if_pos hc
                  rewrite [r] at hite'
                  exact Or.inr hite'
  | Or.inr hnc => exact Or.inl hnc

theorem cnfItePos2 : ∀ {c a b : Prop}, ¬ (ite c a b) ∨ c ∨ b   := by
  intros c a b
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match Classical.em c with
  | Or.inr hnc => have r: (if c then a else b) = b := if_neg hnc
                  rewrite [r] at hite'
                  exact Or.inr hite'
  | Or.inl hc  => exact Or.inl hc

theorem cnfItePos3 : ∀ {c a b : Prop}, ¬ (ite c a b) ∨ a ∨ b   := by
  intros c a b
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match Classical.em c with
  | Or.inr hnc => have r: (if c then a else b) = b := if_neg hnc
                  rewrite [r] at hite'
                  exact Or.inr hite'
  | Or.inl hc  => have r: (if c then a else b) = a := if_pos hc
                  rewrite [r] at hite'
                  exact Or.inl hite'

theorem cnfIteNeg1 : ∀ {c a b : Prop}, (ite c a b) ∨ ¬ c ∨ ¬ a := by
  intros c a b
  apply orImplies
  intro hnite
  match Classical.em c with
  | Or.inl hc  => have r: (if c then a else b) = a := if_pos hc
                  rewrite [r] at hnite
                  exact Or.inr hnite
  | Or.inr hnc => exact Or.inl hnc

theorem cnfIteNeg2 : ∀ {c a b : Prop}, (ite c a b) ∨ c ∨ ¬ b   := by
  intros c a b
  apply orImplies
  intro hnite
  match Classical.em c with
  | Or.inr hnc  => have r: (if c then a else b) = b := if_neg hnc
                   rewrite [r] at hnite
                   exact Or.inr hnite
  | Or.inl hc => exact Or.inl hc

theorem cnfIteNeg3 : ∀ {c a b : Prop}, (ite c a b) ∨ ¬ a ∨ ¬ b := by
  intros c a b
  apply orImplies
  intro hnite
  match Classical.em c with
  | Or.inr hnc  => have r: (if c then a else b) = b := if_neg hnc
                   rewrite [r] at hnite
                   exact Or.inr hnite
  | Or.inl hc => have r: (if c then a else b) = a := if_pos hc
                 rewrite [r] at hnite
                 exact Or.inl hnite

theorem congrIte {α : Type} : ∀ {c₁ c₂ : Prop} {t₁ t₂ e₁ e₂ : α} ,
    c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros c₁ c₂ t₁ t₂ e₁ e₂ h₁ h₂ h₃
  rw [h₁, h₂, h₃]

theorem congrHAdd {α β γ : Type} [HAdd α β γ] : ∀ {a₁ a₂ : α} {b₁ b₂ : β},
    a₁ = a₂ → b₁ = b₂ → a₁ + b₁ = a₂ + b₂ := by
  intros a₁ a₂ b₁ b₂ h₁ h₂
  rw [h₁, h₂]

theorem eqResolve {P Q : Prop} : P → (P = Q) → Q := by
  intros h₁ h₂
  rewrite [← h₂]
  exact h₁

theorem dupOr {P Q : Prop} : P ∨ P ∨ Q → P ∨ Q := λ h =>
  match h with
  | Or.inl p          => Or.inl p
  | Or.inr (Or.inl p) => Or.inl p
  | Or.inr (Or.inr q) => Or.inr q

theorem dupOr₂ {P : Prop} : P ∨ P → P := λ h =>
  match h with
  | Or.inl p => p
  | Or.inr p => p

def andElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name)
  : MetaM MVarId :=
    mvar.withContext do
      let mut pf ← getProof i val
      let type ← inferType val
      let binderName ← getFirstBinderName type
      let env ← getEnv
      let andProp : Expr := 
        match (env.find? binderName).get!.value? with
        | none => type
        | some e => recGetLamBody e
      if i < getLengthAnd andProp - 1 then
        pf ← mkAppM ``And.left #[pf]
      let goal ← inferType pf
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal pf
      return mvar'
where
  recGetLamBody (e : Expr) : Expr :=
    match e with
    | lam _ _ b _ => recGetLamBody b
    | e => e
  getProof (i : Nat) (hyp : Expr) : MetaM Expr :=
    match i with
    | 0 => pure hyp
    | (i + 1) => do
      let rc ← getProof i hyp
      mkAppM ``And.right #[rc]

syntax (name := andElim) "andElim" term "," term : tactic
@[tactic andElim] def evalAndElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile] m!"[andElim] start time: {← IO.monoMsNow}ms"
    let mvar ← getMainGoal
    let val ← elabTerm stx[1] none
    let idx: Term := ⟨stx[3]⟩
    let i ← stxToNat idx
    let fname ← mkFreshId
    let mvar' ← andElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile] m!"[andElim] end time: {← IO.monoMsNow}ms"

def notOrElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name)
  : MetaM MVarId :=
    mvar.withContext do
      let type ← inferType val
      let orChain := notExpr type
      let props ← collectPropsInOrChain orChain
      let prop := props.get! i
      withLocalDeclD (← mkFreshId) prop $ fun bv => do
        let pf: Expr ←
          match (← getLength orChain) == i + 1 with
          | true  => pure bv
          | false =>
            let rest ← createOrChain (props.drop (i + 1))
            mkAppOptM ``Or.inl #[none, rest, bv]
        let pf ← getProof i 0 props pf
        let pf := mkApp val pf
        let pf ← mkLambdaFVars #[bv] pf
        let notProp := mkApp (mkConst ``Not) prop
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name notProp pf
        return mvar'
where
  getProof (i j : Nat) (props : List Expr) (val : Expr) : MetaM Expr :=
    match i with
    | 0     => pure val
    | i + 1 => do
      let currProp := props.get! j
      mkAppOptM ``Or.inr #[currProp, none, ← getProof i (j + 1) props val]

syntax (name := notOrElim) "notOrElim" term "," term : tactic
@[tactic notOrElim] def evalNotOrElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile] m!"[notOrElim] start time: {← IO.monoMsNow}ms"
    let i ← stxToNat ⟨stx[3]⟩
    let val ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← notOrElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile] m!"[notOrElim] end time: {← IO.monoMsNow}ms"

theorem notAnd : ∀ (l : List Prop), ¬ andN l → orN (notList l) := by
  intros l h
  match l with
  | []         => exact False.elim (h True.intro)
  | [_]        => exact h
  | p₁::p₂::ps => simp [orN, notList, map]
                  match deMorganSmall₃ h with
                  | Or.inl hnp₁ => exact Or.inl hnp₁
                  | Or.inr hnAndTail =>
                    have IH := notAnd (p₂::ps) hnAndTail
                    exact Or.inr IH

syntax "flipNotAnd " term ("[" term,* "]")? : term
macro_rules
| `(flipNotAnd $premiss:term [ $[$x:term],* ]) => `(notAnd [ $[$x],* ] $premiss)

theorem modusPonens : ∀ {A B : Prop}, A → (A → B) → B := λ x f => f x

theorem trueIntro : ∀ {A : Prop}, A → A = True := by
  intros A h
  exact propext (Iff.intro (λ _ => True.intro) (λ _ => h))

theorem trueElim : ∀ {A : Prop}, A = True → A := by
  intros A h
  rewrite [h]
  trivial
theorem trueElim₂ : ∀ {A : Prop}, True = A → A :=
  trueElim ∘ Eq.symm

theorem falseIntro : ∀ {A : Prop}, ¬ A → A = False :=
  λ h => propext (Iff.intro (λ a => h a) (λ ff => False.elim ff))
theorem falseIntro₂ : ∀ {A : Prop}, ¬ A → False = A := Eq.symm ∘ falseIntro

theorem falseElim : ∀ {A : Prop}, A = False → ¬ A := λ h ha =>
  match h with
  | rfl => ha
theorem falseElim₂ : ∀ {A : Prop}, False = A → ¬ A := falseElim ∘ Eq.symm

theorem negSymm {α : Type u} {a b : α} : a ≠ b → b ≠ a := λ h f => h (Eq.symm f)

syntax "flipCongrArg " term ("[" term "]")? : term
macro_rules
| `(flipCongrArg $premiss:term [$arg:term]) => `(congrArg $arg $premiss)

syntax "smtIte" (term)? (term)? (term)? (term)? : term
macro_rules
| `(smtIte $cond $t $e $type) => `(term| @ite $type $cond (propDecidable $cond) $t $e)

end Smt.Reconstruction.Certifying
