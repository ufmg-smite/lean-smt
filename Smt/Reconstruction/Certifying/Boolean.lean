/-Theorems for boolean rules-/
import Lean
import Smt.Reconstruction.Certifying.Util

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Expr Classical
open Lean.Elab.Term

open Nat List

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
     | Or.inl pp => match em q with
                    | Or.inl pq => Or.inr pq
                    | Or.inr npq => False.elim (npq (h pp))
     | Or.inr npp => Or.inl npp
 
def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q := scope
 
theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match em p, em q with
     | Or.inl pp,  Or.inl _   => False.elim (h (Or.inl pp))
     | Or.inl pp,  Or.inr _   => False.elim (h (Or.inl pp))
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

theorem doubleNeg : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem doubleNeg₂ : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p
 
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
                       have t₁' := doubleNeg t₁
                       exact ⟨ t₁', ih ⟩
 
theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notList l) :=
  by intros l h
     exact match l with
     | [] => by simp [orN, notList]
     | [t] => by simp [orN, notList]; simp [andN] at h; exact doubleNeg₂ h
     | h₁::h₂::t => by simp [orN, notList, map]
                       simp [andN] at h
                       apply deMorganSmall₂
                       have nnh₁ := doubleNeg₂ (And.left h)
                       have ih := @deMorgan₂ (h₂::t) (And.right h)
                       exact ⟨nnh₁, ih⟩

theorem cnfAndNeg : ∀ (l : List Prop), andN l ∨ orN (notList l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h
 
theorem lessThanOne : ∀ {i : Nat}, i < 1 → i = 0 := by
  intros i h
  match i with
  | zero => exact rfl
  | succ i' =>
    cases h with
    | step h' => cases h'

def getProp : List Prop → Nat → Prop
  | [], _ => True
  | a::_, 0 => a
  | _::as, (i + 1) => getProp as i

theorem cnfAndPos : ∀ (l : List Prop) (i : Nat),  ¬ (andN l) ∨ getProp l i :=
  by intros l i
     apply orImplies
     intro h
     have h' := doubleNeg h
     match l with
     | [] => exact True.intro
     | [p] =>
       match i with
       | 0 => exact h'
       | _ + 1 => exact True.intro
     | p₁::p₂::ps =>
       match i with
       | zero => exact And.left h' 
       | succ i' =>
         simp [getProp]
         have IH :=  cnfAndPos (p₂::ps) i'
         exact orImplies₂ IH (And.right h')

theorem smtCong : ∀ {A B : Type u} {f₁ f₂ : A → B} {t₁ t₂ : A},
  f₁ = f₂ → t₁ = t₂ → f₁ t₁ = f₂ t₂ :=
  by intros A B f₁ f₂ t₁ t₂ h₁ h₂
     rewrite [h₁, h₂]
     exact rfl

def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (take n props)
          let right := createOrChain (drop n props)
          app (app (mkConst `Or) left) right

syntax (name := groupOrPrefix) "groupOrPrefix" term "," term "," ident : tactic

-- supposed to be used by other rules
@[tactic groupOrPrefix] def evalGroupOrPrefix : Tactic := fun stx => withMainContext do
  let hyp ← Tactic.elabTerm stx[1] none
  let prefLen ← 
    match ← getNatLit? <$> Tactic.elabTerm stx[3] none with
    | Option.some i => pure i
    | Option.none   => throwError "[groupOrPrefix]: second argument must be a nat lit"
  let type ← Meta.inferType hyp
  let l := getLength type
  if prefLen > 1 && prefLen < l then
    let mvarId ← getMainGoal
    Meta.withMVarContext mvarId do
      let name := stx[5].getId
      let newTerm := getGroupOrPrefixGoal type prefLen
      let p ← Meta.mkFreshExprMVar newTerm MetavarKind.syntheticOpaque name
      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name newTerm p
      replaceMainGoal [p.mvarId!, mvarIdNew]
    for t in reverse (getCongAssoc (prefLen - 1) `orAssocDir) do
      evalTactic  (← `(tactic| apply $t))
    Tactic.closeMainGoal hyp
  else throwError "[groupOrPrefix]: prefix length must be > 1 and < size of or-chain"

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

-- supposed to be used alone
@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => withMainContext do
    -- TODO: don't repeat this
    let prefLen ← 
      match ← getNatLit? <$> Tactic.elabTerm stx[3] none with
      | Option.some i => pure i
      | Option.none   => throwError "[liftNOrToImp]: second argument must be a nat lit"
    let tstx₁ : Term := ⟨stx[1]⟩
    let tstx₃ : Term := ⟨stx[3]⟩
    let fname1 ← mkIdent <$> mkFreshId
    let hyp ← inferType (← Tactic.elabTerm stx[1] none)
    let _ ← evalTactic (← `(tactic| groupOrPrefix $tstx₁, $tstx₃, $fname1))
    let fname2 ← mkIdent <$> mkFreshId
    let _ ← evalTactic (← `(tactic| intros $fname2))
    let _ ← evalTactic (← `(tactic| apply orImplies₃ $fname1))
    let li := listExpr (collectNOrNegArgs hyp prefLen) (Expr.sort Level.zero)
    withMainContext do
      let ctx ← getLCtx
      let a := (ctx.findFromUserName? fname2.getId).get!.toExpr
      let u : Expr := mkApp (mkApp (mkConst `deMorgan₂) li) a
      Tactic.closeMainGoal u

theorem eqResolve {P Q : Prop} : P → P = Q → Q := by
  intros h₁ h₂
  rewrite [← h₂]
  exact h₁

