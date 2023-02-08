import Lean

import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Options

open Lean Elab.Tactic Meta Expr Syntax
open Nat List Classical

/- abbrev Implies (p q : Prop) := p → q -/

namespace Smt.Reconstruction.Certifying.Macro

open Lean.Macro

scoped syntax (name := binder) "(" binderIdent term ")" : term
scoped syntax (name := binders) binder+ : term

scoped macro "forall " "(" xs:binders ")" b:term : term => match xs with
  | `(binders| $[($x:ident $t:term)]*) => `(term| ∀ $[($x : $t)]*, $b)
  | _ => throwUnsupported

scoped macro "exists " "(" xs:binders ")" b:term : term => match xs with
  | `(binders| $[($x:binderIdent $t:term)]*) => `(term| ∃ $[($x : $t)]*, $b)
  | _ => throwUnsupported

end Smt.Reconstruction.Certifying.Macro

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem equivElim1 : ∀ {P Q : Prop}, Eq P Q → ¬ P ∨ Q := by
  intros P Q h
  rewrite [h]
  cases em Q with
  | inl q  => exact Or.inr q
  | inr nq => exact Or.inl nq

theorem equivElim2 : ∀ {P Q : Prop}, Eq P Q → P ∨ ¬ Q := by
  intros P Q h
  rewrite [h]
  cases em Q with
  | inl q  => exact Or.inl q
  | inr nq => exact Or.inr nq

theorem notEquivElim1 : ∀ {P Q : Prop}, ¬ (Eq P Q) → P ∨ Q := by
  intros P Q h
  exact match em P, em Q with
  | Or.inl p, _ => Or.inl p
  | _, Or.inl q => Or.inr q
  | Or.inr np, Or.inr nq =>
    absurd (propext (Iff.intro (λ p => absurd p np) (λ q => absurd q nq))) h

theorem notEquivElim2 : ∀ {P Q : Prop}, ¬ (Eq P Q) → ¬ P ∨ ¬ Q := by
  intros P Q h
  exact match em P, em Q with
  | Or.inr np, _ => Or.inl np
  | _, Or.inr nq => Or.inr nq
  | Or.inl p, Or.inl q =>
    absurd (propext (Iff.intro (λ _ => q) (λ _ => p))) h

theorem iteElim1 : ∀ {c a b : Prop}, ite c a b → ¬ c ∨ a := by
  intros c a b h
  cases em c with
  | inl hc => have r: ite c a b = a := if_pos hc
              rewrite [r] at h
              exact Or.inr h
  | inr hnc => exact Or.inl hnc

theorem iteElim2 : ∀ {c a b : Prop}, ite c a b → c ∨ b := by
  intros c a b h
  cases em c with
  | inl hc => exact Or.inl hc
  | inr hnc => have r: ite c a b = b := if_neg hnc
               rewrite [r] at h
               exact Or.inr h

theorem notIteElim1 : ∀ {c a b : Prop}, ¬ ite c a b → ¬ c ∨ ¬ a := by
  intros c a b h
  cases em c with
  | inl hc  => have r : ite c a b = a := if_pos hc
               rewrite [r] at h
               exact Or.inr h
  | inr hnc => exact Or.inl hnc

theorem notIteElim2 : ∀ {c a b : Prop}, ¬ ite c a b → c ∨ ¬ b := by
  intros c a b h
  cases em c with
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

theorem congOrLeft : ∀ {R P Q : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match em q with
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
     exact match em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q := scope

theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match em p, em q with
     | Or.inl pp,  _          => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq

theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match em p, em q with
     | Or.inl pp,  _   => False.elim (np pp)
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp)
                                    | Or.inr pq => False.elim (npq pq)

theorem deMorganSmall₃ : ∀ {p q : Prop}, ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  by intros p q h
     match em p, em q with
     | Or.inl hp, Or.inl hq  => exact False.elim (h (And.intro hp hq))
     | _,         Or.inr hnq => exact Or.inr hnq
     | Or.inr hnp, _        => exact Or.inl hnp

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem notNotIntro : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p

theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notList l) → andN l :=
  by intros l h
     exact match l with
     | []   => True.intro
     | [t]  => by simp [andN]
                  simp [notList, orN, map] at h
                  cases em t with
                  | inl tt  => exact tt
                  | inr ntt => exact False.elim (h ntt)
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
     | [t] => by simp [orN, notList]; simp [andN] at h; exact notNotIntro h
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

syntax (name := cnfAndNegT) "cnfAndNegT" ("[" term,* "]")? : tactic

def parseCnfAndNeg : Syntax → TacticM Expr
  | `(tactic| cnfAndNegT [ $[$hs],* ]) => do
    let each ← Array.mapM (fun h => elabTerm h none) hs
    let li := listExpr each.data (Expr.sort Level.zero)
    return li
  | _ => throwError "[cnfAndNeg]: wrong usage"

@[tactic cnfAndNegT] def evalCnfAndNegT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let e ← parseCnfAndNeg stx
    closeMainGoal (mkApp (mkConst `cnfAndNeg) e)
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[cnfAndNeg] Time taken: {endTime - startTime}ms"

syntax (name := cnfAndPosT) "cnfAndPosT" ("[" term,* "]")? "," term : tactic

def parseCnfAndPos : Syntax → TacticM (Expr × Expr)
  | `(tactic| cnfAndPosT [ $[$hs],* ], $i) => do
    let each ← Array.mapM (fun h => elabTerm h none) hs
    let li := listExpr each.data (Expr.sort Level.zero)
    let i' ← elabTerm i none
    return (li, i')
  | _ => throwError "[cnfAndPos]: wrong usage"

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

@[tactic cnfAndPosT] def evalCnfAndPosT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let (li, i) ← parseCnfAndPos stx
    closeMainGoal $ mkApp (mkApp (mkConst `cnfAndPos) li) i
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[cnfAndPos]: Time taken: {endTime - startTime}ms"

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

theorem cnfOrPos : ∀ (l : List Prop), ¬ orN l ∨ orN l := λ l => orComm (em (orN l))

theorem cnfImpliesPos : ∀ {p q : Prop}, ¬ (p → q) ∨ ¬ p ∨ q := by
  intros p q
  match em p, em q with
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
  match em c with
  | Or.inl hc  => have r: (if c then a else b) = a := if_pos hc
                  rewrite [r] at hite'
                  exact Or.inr hite'
  | Or.inr hnc => exact Or.inl hnc

theorem cnfItePos2 : ∀ {c a b : Prop}, ¬ (ite c a b) ∨ c ∨ b   := by
  intros c a b
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match em c with
  | Or.inr hnc => have r: (if c then a else b) = b := if_neg hnc
                  rewrite [r] at hite'
                  exact Or.inr hite'
  | Or.inl hc  => exact Or.inl hc

theorem cnfItePos3 : ∀ {c a b : Prop}, ¬ (ite c a b) ∨ a ∨ b   := by
  intros c a b
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match em c with
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
  match em c with
  | Or.inl hc  => have r: (if c then a else b) = a := if_pos hc
                  rewrite [r] at hnite
                  exact Or.inr hnite
  | Or.inr hnc => exact Or.inl hnc

theorem cnfIteNeg2 : ∀ {c a b : Prop}, (ite c a b) ∨ c ∨ ¬ b   := by
  intros c a b
  apply orImplies
  intro hnite
  match em c with
  | Or.inr hnc  => have r: (if c then a else b) = b := if_neg hnc
                   rewrite [r] at hnite
                   exact Or.inr hnite
  | Or.inl hc => exact Or.inl hc

theorem cnfIteNeg3 : ∀ {c a b : Prop}, (ite c a b) ∨ ¬ a ∨ ¬ b := by
  intros c a b
  apply orImplies
  intro hnite
  match em c with
  | Or.inr hnc  => have r: (if c then a else b) = b := if_neg hnc
                   rewrite [r] at hnite
                   exact Or.inr hnite
  | Or.inl hc => have r: (if c then a else b) = a := if_pos hc
                 rewrite [r] at hnite
                 exact Or.inl hnite

theorem smtCong₁ : ∀ {A B : Type u} {f₁ f₂ : A → B} {t₁ t₂ : A},
  f₁ = f₂ → t₁ = t₂ → f₁ t₁ = f₂ t₂ := congr

theorem smtCong₂ : ∀ {B : Type u} {f₁ f₂ : Prop → B} {t₁ t₂ : Prop},
  f₁ = f₂ → (t₁ ↔ t₂) → f₁ t₁ = f₂ t₂ :=
  by intros B f₁ f₂ t₁ t₂ h₁ h₂
     rewrite [h₁, h₂]
     exact rfl

theorem smtCong₃ : ∀ {A : Type u} {f₁ f₂ : A → Prop} {t₁ t₂ : A},
  (f₁ = f₂) → (t₁ = t₂) → (f₁ t₁ ↔ f₂ t₂) :=
  by intros A f₁ f₂ t₁ t₂ h₁ h₂
     rewrite [h₁, h₂]
     exact Iff.rfl

theorem smtCong₄ : ∀ {f₁ f₂ : Prop → Prop} {t₁ t₂ : Prop},
  f₁ = f₂ → (t₁ ↔ t₂) → (f₁ t₁ ↔ f₂ t₂) :=
  by intros f₁ f₂ t₁ t₂ h₁ h₂
     rewrite [h₁, h₂]
     exact Iff.rfl

syntax (name := congrT) "congrT" term "," term : tactic
@[tactic congrT] def evalCongrT : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let h₁ := ⟨stx[1]⟩
    let h₂ := ⟨stx[3]⟩
    evalTactic (← `(tactic| exact congr $h₁ $h₂))
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[congrT]: Time taken: {endTime - startTime}ms"

syntax (name := smtCong) "smtCong" term "," term : tactic
@[tactic smtCong] def evalSmtCong : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let hyp2 ← elabTerm stx[3] none
    let hyp2Type ← inferType hyp2
    let t1: Term := ⟨stx[1]⟩
    let t3: Term := ⟨stx[3]⟩
    let e₁ ← elabTerm t1 none
    let t₁ ← instantiateMVars (← inferType e₁)
    let d ← getFunctionCounterDomain t₁
    let isProp := d == sort Level.zero
    match isProp, isIff hyp2Type with
    | false, false => evalTactic (← `(tactic| exact smtCong₁ $t1 $t3))
    | false, true  => evalTactic (← `(tactic| exact smtCong₁ $t1 $t3))
    | true,  false => evalTactic (← `(tactic| exact smtCong₁ $t1 $t3))
    | true,  true  => evalTactic (← `(tactic| exact smtCong₁ $t1 $t3))
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[smtCong] Time taken: {endTime - startTime}ms"
where
  isIff : Expr → Bool
  | app (app (const `Iff ..) _) _ => true
  | _ => false
  getFunctionCounterDomain : Expr → TacticM Expr
  | app (app _ e₁) _ => do
    let t₁ ← inferType e₁
    let d₁ := bindingBody! t₁
    return d₁
  | _ => throwError "unexpected type in smtCong"

theorem congrIte {α : Type} : ∀ {c₁ c₂ : Prop} {t₁ t₂ e₁ e₂ : α} ,
  c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros c₁ c₂ t₁ t₂ e₁ e₂ h₁ h₂ h₃
  rw [h₁, h₂, h₃]

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

syntax (name := andElim) "andElim" term "," term : tactic
@[tactic andElim] def evalAndElim : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let i ← stxToNat ⟨stx[3]⟩
    let mut proof := getProof i stx[1]
    let andProp ← inferType (← elabTerm stx[1] none)
    if i < getLengthAnd andProp - 1 then
      proof := Syntax.mkApp (mkIdent `And.left) #[⟨proof⟩]
    let proofE ← elabTerm proof none
    closeMainGoal proofE
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[andElim] Time taken: {endTime - startTime}ms"
where
  getProof (i : Nat) (hyp : Syntax) : Syntax :=
    match i with
    | 0 => hyp
    | (i + 1) =>
      Syntax.mkApp (mkIdent `And.right) #[⟨getProof i hyp⟩]

example : A ∧ B ∧ C ∧ D → D := by
  intro h
  andElim h, 3

syntax (name := notOrElim) "notOrElim" term "," term : tactic
@[tactic notOrElim] def evalNotOrElim : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  withMainContext do
    let i ← stxToNat ⟨stx[3]⟩
    let hyp ← inferType (← elabTerm stx[1] none)
    let orChain := notExpr hyp
    let proof: Syntax ←
      match getLength orChain == i + 1 with
      | true => `(x)
      | false => `(Or.inl x)
    let proof: Syntax := getProof i proof
    let proof := Syntax.mkApp ⟨stx[1]⟩ #[⟨proof⟩]
    let proof ← `(fun x => $proof)
    let proofE ← elabTerm proof none
    closeMainGoal proofE
  let endTime ← IO.monoMsNow
  trace[smt.profile] m!"[notOrElim] Time taken: {endTime - startTime}ms"
where
  getProof (i : Nat) (hyp : Syntax) : Syntax :=
    match i with
    | 0 => hyp
    | i + 1 => Syntax.mkApp (mkIdent `Or.inr) #[⟨getProof i hyp⟩]

example : ¬ (A ∨ B ∨ C ∨ D) → ¬ C := by
  intro h
  notOrElim h, 2

syntax (name := reportTimeOfTactic) "reportTimeOfTactic" term "," term : tactic
@[tactic reportTimeOfTactic] def evalReportTimeOfTactic : Tactic := fun stx => do
  let time ← IO.monoMsNow
  trace[smt.profile] s!"tactic {stx[1]} produced {stx[3]} at {time}ms"

syntax (name := reportTime) "reportTime" : tactic
@[tactic reportTime] def evalReport : Tactic := fun _ => do
  let time ← IO.monoMsNow
  trace[smt.profile] s!"{time}ms"

theorem notAnd : ∀ (l : List Prop), ¬ andN l → orN (notList l) := by
  intros l h
  match l with
  | []         => exact False.elim (h True.intro)
  | [_]        => exact h
  | p₁::p₂::ps => simp [andN] at h
                  simp [orN, notList, map]
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
