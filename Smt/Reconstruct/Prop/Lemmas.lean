/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct.Util

namespace Smt.Reconstruct.Prop

open Lean Elab.Tactic Meta Expr Syntax
open Nat List Classical

theorem ite_eq (c : Prop) [h : Decidable c] (x y : α) : ite c ((ite c x y) = x) ((ite c x y) = y) := by
  cases h
  all_goals simp_all

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

theorem xorElim1 (h : XOr p q) : p ∨ q :=
  match h with
  | .inl hp _ => Or.inl hp
  | .inr _ hq => Or.inr hq

theorem xorElim2 (h : XOr p q) : ¬p ∨ ¬q :=
  match h with
  | .inl _ hnq => Or.inr hnq
  | .inr hnp _ => Or.inl hnp

theorem notXorElim1 (h : ¬XOr p q) : p ∨ ¬q :=
  match Classical.em p, Classical.em q with
  | Or.inl hp, _ => Or.inl hp
  | _, Or.inr hnq => Or.inr hnq
  | Or.inr hnp, Or.inl hq =>
    absurd (.inr hnp hq) h

theorem notXorElim2 (h : ¬XOr p q) : ¬p ∨ q :=
  match Classical.em p, Classical.em q with
  | Or.inr hnp, _ => Or.inl hnp
  | _, Or.inl hq => Or.inr hq
  | Or.inl hp, Or.inr hnq =>
    absurd (.inl hp hnq) h

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

def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

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
     | [t]  => by simp only [andN]
                  simp only [notList, orN, map] at h
                  cases Classical.em t with
                  | inl tt  => exact tt
                  | inr ntt => exact False.elim (h ntt)
     | h₁::h₂::t => by simp [orN, notList, map] at h
                       have ⟨ t₁, t₂ ⟩ := deMorganSmall h
                       have ih := @deMorgan (h₂::t) t₂
                       simp [andN]
                       have t₁' := notNotElim t₁
                       exact ⟨ t₁', ih ⟩

theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notList l) :=
  by intros l h
     exact match l with
     | [] => by simp [orN, notList]
     | [t] => by simp only [orN, notList]; simp [andN] at h; exact notNotIntro h
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

theorem cnfAndNeg' : ∀ (l : List Prop), andN l ∨ orN (notList l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h

theorem cnfAndNeg : orN (andN l :: notList l) := by
  cases l with
  | nil => trivial
  | cons l ls =>
    simp only [orN]
    apply cnfAndNeg'

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

theorem cnfOrPos' : ∀ (l : List Prop), ¬ orN l ∨ orN l := λ l => orComm (Classical.em (orN l))

theorem cnfOrPos : orN ((¬orN l) :: l) := by
  cases l with
  | nil => exact not_false
  | cons l ls =>
    simp only [orN]
    apply cnfOrPos'

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

theorem cnfEquivPos1 : ∀ {p q : Prop}, p ≠ q ∨ ¬ p ∨ q := by
  intros _ _
  apply orImplies
  exact equivElim1 ∘ notNotElim

theorem cnfEquivPos2 : ∀ {p q : Prop}, p ≠ q ∨ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact equivElim2 ∘ notNotElim

theorem cnfEquivNeg1 : ∀ {p q : Prop}, p = q ∨ p ∨ q := by
  intros _ _
  apply orImplies
  exact notEquivElim1

theorem cnfEquivNeg2 : ∀ {p q : Prop}, p = q ∨ ¬ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact notEquivElim2

theorem cnfXorPos1 : ¬(XOr p q) ∨ p ∨ q :=
  orImplies (xorElim1 ∘ notNotElim)

theorem cnfXorPos2 : ¬(XOr p q) ∨ ¬p ∨ ¬q :=
  orImplies (xorElim2 ∘ notNotElim)

theorem cnfXorNeg1 : (XOr p q) ∨ ¬p ∨ q :=
  orImplies notXorElim2

theorem cnfXorNeg2 : (XOr p q) ∨ p ∨ ¬q :=
  orImplies notXorElim1

theorem iteIntro {α : Type u} {c : Prop} {t e : α} : ite c ((ite c t e) = t) ((ite c t e) = e) := by
  match Classical.em c with
  | Or.inl hc  => rw [if_pos hc, if_pos hc]
  | Or.inr hnc => rw [if_neg hnc, if_neg hnc]

theorem congrIte [Decidable c₁] [Decidable c₂] {t₁ t₂ e₁ e₂ : α} :
    c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros h₁ h₂ h₃
  simp only [h₁, h₂, h₃]

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

theorem and_elim (hps : andN ps) (i : Nat) {hi : i < ps.length} : ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => hps.left
    | i + 1 => Eq.symm (List.cons_getElem_succ p₁ (p₂ :: ps) i hi) ▸ and_elim hps.right i

theorem not_or_elim (hnps : ¬orN ps) (i : Nat) {hi : i < ps.length} : ¬ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hnps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => (deMorganSmall hnps).left
    | i + 1 => Eq.symm (List.cons_getElem_succ p₁ (p₂ :: ps) i hi) ▸ not_or_elim (deMorganSmall hnps).right i

def andElimMeta (mvar : MVarId) (val : Expr) (i : Nat) (name : Name)
  : MetaM MVarId :=
    mvar.withContext do
      let mut pf ← getProof i val
      let type ←  inferType val
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

def andElim (mv : MVarId) (val : Expr) (i : Nat) : MetaM Unit :=
    mv.withContext do
      let mut pf ← getProof i val
      let type ←  inferType val
      let binderName ← getFirstBinderName type
      let env ← getEnv
      let andProp : Expr :=
        match (env.find? binderName).get!.value? with
        | none => type
        | some e => recGetLamBody e
      if i < getLengthAnd andProp - 1 then
        pf ← mkAppM ``And.left #[pf]
      mv.assign pf
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

namespace Tactic

syntax (name := andElim) "andElim" term "," term : tactic
@[tactic andElim] def evalAndElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile.reconstruct] m!"[andElim] start time: {← IO.monoNanosNow}ns"
    let mvar ← getMainGoal
    let val ← elabTerm stx[1] none
    let idx: Term := ⟨stx[3]⟩
    let i ← stxToNat idx
    let fname ← mkFreshId
    let mvar' ← andElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[andElim] end time: {← IO.monoNanosNow}ns"

end Tactic

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

def traceNotOrElim (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

def notOrElim (mv : MVarId) (val : Expr) (i : Nat) : MetaM Unit := withTraceNode `smt.reconstruct.notOrElim traceNotOrElim do
    mv.withContext do
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
        mv.assign pf
where
  getProof (i j : Nat) (props : List Expr) (val : Expr) : MetaM Expr :=
    match i with
    | 0     => pure val
    | i + 1 => do
      let currProp := props.get! j
      mkAppOptM ``Or.inr #[currProp, none, ← getProof i (j + 1) props val]

namespace Tactic

syntax (name := notOrElim) "notOrElim" term "," term : tactic
@[tactic notOrElim] def evalNotOrElim : Tactic := fun stx => do
  withMainContext do
    trace[smt.profile.reconstruct] m!"[notOrElim] start time: {← IO.monoNanosNow}ns"
    let i ← stxToNat ⟨stx[3]⟩
    let val ← elabTerm stx[1] none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← notOrElimMeta mvar val i fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.profile.reconstruct] m!"[notOrElim] end time: {← IO.monoNanosNow}ns"

end Tactic

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

theorem trueImplies {p : Prop} : (True → p) → p := by
  intro htp
  exact htp trivial

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

theorem eq_not_not (p : Prop) : p = ¬¬p := propext (not_not.symm)

theorem orN_cons : orN (t :: l) = (t ∨ orN l) := by
  cases l with
  | nil => simp [orN]
  | cons t' l => simp [orN]

theorem orN_eraseIdx (hj : j < qs.length) : (orN (qs.eraseIdx j) ∨ qs[j]) = (orN qs) := by
  revert j
  induction qs with
  | nil =>
    intro j hj
    simp at hj; exfalso
    exact not_succ_le_zero j hj
  | cons t l ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [eraseIdx_cons_zero, cons_getElem_zero, orN_cons, eraseIdx_cons_succ, cons_getElem_succ]
      rw [or_comm]
    | succ j =>
      simp only [eraseIdx_cons_succ, cons_getElem_succ, orN_cons, eraseIdx, or_assoc]
      congr
      rw [@ih j (by rw [length_cons, succ_lt_succ_iff] at hj; exact hj)]

def subList' (xs : List α) (i j : Nat) : List α :=
  List.drop i (xs.take j)

theorem orN_subList (hps : orN ps) (hpq : ps = subList' qs i j): orN qs := by
  revert i j ps
  induction qs with
  | nil =>
    intro ps i j hp hps
    simp [subList', *] at *; assumption
  | cons t l ih =>
    simp only [subList'] at *
    intro ps i j hp hps
    rw [orN_cons]
    cases j with
    | zero =>
      simp [*, orN] at *
    | succ j =>
      simp only [take_cons_succ] at hps
      cases i with
      | zero =>
        simp only [hps, orN_cons, drop_zero] at hp
        exact congOrLeft (fun hp => @ih (drop 0 (take j l)) 0 j (by simp [hp]) rfl) hp
      | succ i =>
        apply Or.inr
        apply @ih ps i j hp
        simp [hps]

theorem length_take (h : n ≤ l.length) : (take n l).length = n := by
  revert n
  induction l with
  | nil => intro n h; simp at h; simp [h]
  | cons t l ih =>
    intro n h
    cases n with
    | zero => simp
    | succ n => simp [ih (by rw [length_cons, succ_le_succ_iff] at h; exact h)]

theorem length_eraseIdx (h : i < l.length) : (eraseIdx l i).length = l.length -1 := by
  revert i
  induction l with
  | nil => simp
  | cons t l ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      simp
      rw [length_cons, succ_lt_succ_iff] at hi
      rw [ih hi, Nat.succ_eq_add_one, Nat.sub_add_cancel (zero_lt_of_lt hi)]

theorem take_append (a b : List α) : take a.length (a ++ b) = a := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).1
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem drop_append (a b : List α): drop a.length (a ++ b) = b := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).2
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem orN_append_left (hps : orN ps) : orN (ps ++ qs) := by
  apply @orN_subList ps (ps ++ qs) 0 ps.length hps
  simp [subList', take_append]

theorem orN_append_right (hqs : orN qs) : orN (ps ++ qs) := by
  apply @orN_subList qs (ps ++ qs) ps.length (ps.length + qs.length) hqs
  simp only [←length_append, subList', take_length, drop_append]

theorem orN_resolution (hps : orN ps) (hqs : orN qs) (hi : i < ps.length) (hj : j < qs.length) (hij : ps[i] = ¬qs[j]) : orN (ps.eraseIdx i ++ qs.eraseIdx j) := by
  have H1 := orN_eraseIdx hj
  have H2 := orN_eraseIdx hi
  by_cases h : ps[i]
  · simp only [eq_iff_iff, true_iff, iff_true, h, hqs, hij, hps] at *
    apply orN_append_right (by simp [*] at *; exact H1)
  · simp only [hps, hqs, h, eq_iff_iff, false_iff, not_not, iff_true, or_false,
    not_false_eq_true] at *
    apply orN_append_left H2

theorem implies_of_not_and : ¬(andN' ps ¬q) → impliesN ps q := by
  induction ps with
  | nil => exact notNotElim
  | cons p ps ih =>
    simp only [andN', impliesN]
    intro hnpps hp
    have hnpnps := deMorganSmall₃ hnpps
    match hnpnps with
    | .inl hnp => contradiction
    | .inr hnps => exact ih hnps

syntax "flipCongrArg " term ("[" term "]")? : term
macro_rules
| `(flipCongrArg $premiss:term [$arg:term]) => `(congrArg $arg $premiss)

syntax "smtIte" (term)? (term)? (term)? (term)? : term
macro_rules
| `(smtIte $cond $t $e $type) => `(term| @ite $type $cond (propDecidable $cond) $t $e)

end Smt.Reconstruct.Prop
