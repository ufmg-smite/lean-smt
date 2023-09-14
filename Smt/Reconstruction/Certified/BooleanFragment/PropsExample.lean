import Smt.Reconstruction.Certified.Term

open proof
open term

def Interpretation: Type := Nat → Prop

@[simp] def evalTerm (I : Interpretation) (t : term) : Prop :=
  match t with
  | term.const   i  _  => I i
  | term.not     t₁    => Not (evalTerm I t₁)
  | term.and     t₁ t₂ => And (evalTerm I t₁) (evalTerm I t₂)
  | term.or      t₁ t₂ => Or (evalTerm I t₁) (evalTerm I t₂)
  | term.implies t₁ t₂ => (evalTerm I t₁) -> (evalTerm I t₂)
  | term.eq      t₁ t₂ => (evalTerm I t₁) = (evalTerm I t₂)
  | term.bot           => False
  | term.top           => True
  | _                  => False

@[simp] def satisfies (I : Interpretation) (t : term) : Prop :=
  evalTerm I t = True

@[simp] def impliesIn (t₁ t₂ : term) : Prop :=
  ∀ {I : Interpretation}, satisfies I t₁ → satisfies I t₂

/- -- Used Lemmas -/

theorem eqTrue {A : Prop} : A = True → A := fun ha => by rw [ha]; exact True.intro

theorem eqFalse {A : Prop} : A = False → ¬ A := fun hna => by rw [hna]; simp

theorem impliesEqTrue {A : Prop} : A → (A = True) := fun ha =>
  propext $ Iff.intro (fun _ => True.intro) (fun _ => ha)

theorem impliesEqFalse {A : Prop} : ¬ A → (A = False) := fun hna =>
  propext $ Iff.intro (fun ha => hna ha) False.elim

theorem negNegElim {A : Prop} : ¬ ¬ A → A := by
  cases Classical.em A with
  | inl c => exact fun _ => c
  | inr c => exact fun h => False.elim (h c)

/- -- Boolean theorems -/

theorem notImplies1' : ∀ {t₁ t₂ : term},
    impliesIn (not (implies t₁ t₂)) t₁ := by
  intros t₁ t₂ I h
  simp at *
  cases Classical.em (evalTerm I t₁) with
  | inl r => exact impliesEqTrue r
  | inr r => have h' := eqTrue h
             apply False.elim
             apply h'
             intro abs
             apply False.elim
             exact r abs

theorem notImplies2' : ∀ {t₁ t₂ : term},
    impliesIn (not $ implies t₁ t₂) (not t₂) := by
  intros t₁ t₂ I h
  simp at *
  cases Classical.em (evalTerm I t₂) with
  | inl r => have h' := eqTrue h
             apply False.elim
             apply h'
             exact fun _ => r
  | inr r => exact impliesEqTrue r

theorem impliesElim' : ∀ {t₁ t₂: term},
    impliesIn (implies t₁ t₂) (or (not t₁) t₂) := by
  intros t₁ t₂ I h
  simp at *
  apply propext
  apply Iff.intro
  { exact fun _ => True.intro }
  intro _
  have h' := eqTrue h
  cases Classical.em (evalTerm I t₁) with
  | inl c => exact Or.inr (h' c)
  | inr c => exact Or.inl c

theorem contradiction': ∀ {t: term},
    impliesIn (and (not t) t) bot := by
  intros t I h
  simp at *
  have ⟨hna, ha⟩  := eqTrue h
  exact hna ha

theorem R1' : ∀ {t₁ t₂ : term},
    impliesIn (and (or (not t₁) t₂) t₁) t₂ := by
  intros t₁ t₂ I h
  simp at *
  have h' := eqTrue h
  have nT1OrT2 := h'.1
  have t1True := h'.2
  cases nT1OrT2 with
  | inl c => exact False.elim (c t1True)
  | inr c => exact impliesEqTrue c

theorem conjunction: ∀ {t₁ t₂ : term} {I : Interpretation},
    satisfies I t₁ → satisfies I t₂ → satisfies I (and t₁ t₂) := by
  intros t₁ t₂ I h₁ h₂
  simp at *
  apply impliesEqTrue
  exact And.intro (eqTrue h₁) (eqTrue h₂)

/- -- Auxiliary Theorems -/

theorem evalNotTerm: ∀ {I: Interpretation} {t: term},
    evalTerm I (not t) = False → evalTerm I t = True := by
  intros I t h
  simp at *
  apply impliesEqTrue
  exact negNegElim (eqFalse h)

theorem impliesInBot : ∀ {t : term},
    impliesIn t bot → ∀ {I : Interpretation}, evalTerm I t = False := by
  intros t h I
  simp at *
  have h' := @h I
  cases Classical.em (evalTerm I t) with
  | inl c => exact False.elim (h' (impliesEqTrue c))
  | inr c => exact impliesEqFalse c

theorem notImpliesInBot : ∀ {t : term},
    impliesIn (not t) bot → ∀ {I : Interpretation}, evalTerm I t = True := by
  intros t h I
  have h₁ := @impliesInBot (not t) h
  have h₁' := @h₁ I
  exact @evalNotTerm I t h₁'

/- -- Example -/

def p: term := const 1000 boolSort
def q: term := const 1001 boolSort
def modusPonenesEmbed := implies p (implies (implies p q) q)
def notModusPonensEmbed := not modusPonenesEmbed

theorem th0 : impliesIn notModusPonensEmbed bot :=
  λ lean_a0 =>
    have lean_s0 := notImplies2' lean_a0
    have lean_s1 := notImplies1' lean_s0
    have lean_s2 := impliesElim' lean_s1
    have lean_s4 := notImplies1' lean_a0
    have lean_s6 := R1' (conjunction lean_s2 lean_s4)
    have lean_s9 := notImplies2' lean_s0
    contradiction' (conjunction lean_s9 lean_s6)

theorem modusPonensEqTrue: ∀ {I: Interpretation},
    evalTerm I modusPonenesEmbed = True :=
  notImpliesInBot th0

def modusPonens (P Q : Prop) : Prop := P → (P → Q) → Q

theorem modusPonensCorrect: ∀ (P Q: Prop), (modusPonens P Q) = True := by
  intros P Q
  exact @modusPonensEqTrue (fun id => if id == 1000 then P else Q)

-- theorem mpCorrect: ∀ {P Q: Prop}, modusPonens P Q :=
--   eqTrue modusPonensEqTrue
