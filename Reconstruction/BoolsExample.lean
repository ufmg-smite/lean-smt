import Smt.Reconstruction.Term

open proof
open term

@[simp] def bimplies : Bool → Bool → Bool
| true, false => false
| _,    _     => true

def Interpretation: Type := Nat → Bool

@[simp] def interpTerm (f : Interpretation) (t : term) : Bool :=
  match t with
  | term.const   i  _  => f i
  | term.not     t₁    => not $ interpTerm f t₁
  | term.and     t₁ t₂ => and (interpTerm f t₁) (interpTerm f t₂)
  | term.or      t₁ t₂ => or (interpTerm f t₁) (interpTerm f t₂)
  | term.implies t₁ t₂ => bimplies (interpTerm f t₁) (interpTerm f t₂)
  | term.xor     t₁ t₂ => (interpTerm f t₁) != (interpTerm f t₂)
  | term.eq      t₁ t₂ => (interpTerm f t₁) == (interpTerm f t₂)
  | term.bot           => false
  | term.top           => true
  | _                  => false

def followsFrom (t₁ t₂ : term) : Prop :=
  ∀ {f : Interpretation}, interpTerm f t₁ = true → interpTerm f t₂ = true

-- Boolean rules

theorem notImplies1 : ∀ {t₁ t₂ : term},
  followsFrom (not $ implies t₁ t₂) t₁
  | t₁, t₂, f, h =>
    match r₁: interpTerm f t₁, r₂: interpTerm f t₂ with
    | true, _      => rfl
    | false, true  => by simp at h
                         rewrite [r₁, r₂] at h
                         simp at h
    | false, false => by simp at h
                         rewrite [r₁, r₂] at h
                         simp at h

theorem interpNotTerm : ∀ {f : Interpretation} {t : term},
  interpTerm f (not t) = false → interpTerm f t = true
  | f, t, h =>
    match r: interpTerm f t with
    | true  => rfl
    | false => by simp at h
                  rewrite [r] at h
                  simp at h

theorem notImplies2 : ∀ {t₁ t₂ : term},
  followsFrom (not $ implies t₁ t₂) (not t₂)
  | t₁, t₂, f, h => have r₁ := notImplies1 h
    match r₂: interpTerm f (not t₂) with
    | true  => rfl
    | false => by simp at h
                  have r₂' := interpNotTerm r₂
                  rewrite [r₁, r₂'] at h
                  simp at h

theorem impliesElim : ∀ {t₁ t₂: term},
  followsFrom (implies t₁ t₂) (or (not t₁) t₂)
  | t₁, t₂, f, h =>
    match r₁: interpTerm f t₁, r₂: interpTerm f t₂ with
    | false, _     => by simp
                         rewrite [r₁, r₂]
                         exact (Or.inl rfl)
    | true,  false => by simp at h
                         rewrite [r₁, r₂] at h
                         simp at h
    | true,  true  => by simp
                         rewrite [r₁, r₂]
                         exact (Or.inr rfl)

theorem contradiction: ∀ {t: term},
  followsFrom (and (not t) t) bot
  | t, f, h => by simp at h
                  cases r: interpTerm f t with
                  | false => rewrite [r] at h
                             simp at h
                  | true  => rewrite [r] at h
                             simp at h

theorem R1 : ∀ {t₁ t₂ : term},
  followsFrom (and (or (not t₁) t₂) t₁) t₂
  | t₁, t₂, f, h =>
    match r₁: interpTerm f t₁, r₂: interpTerm f t₂ with
    | _,     true  => rfl
    | true,  false => by simp at h
                         rewrite [r₁, r₂] at h
                         simp at h
    | false, false => by simp at h
                         rewrite [r₁, r₂] at h
                         simp at h

theorem conjunction: ∀ {t₁ t₂: term} {f: Interpretation},
  interpTerm f t₁ = true → interpTerm f t₂ = true → interpTerm f (and t₁ t₂)
  | t₁, t₂, f, h₁, h₂ => by simp
                            rewrite [h₁, h₂]
                            exact (And.intro rfl rfl)

-- Example (modus ponens)

def p: term := const 1000 boolSort
def q: term := const 1001 boolSort
def mpDE': term := implies p (implies (implies p q) q)
def notMpDE: term := not mpDE'

theorem th0 : followsFrom notMpDE bot :=
  λ lean_a0 =>
    have lean_s0 := notImplies2 lean_a0
    have lean_s1 := notImplies1 lean_s0
    have lean_s2 := impliesElim lean_s1
    have lean_s4 := notImplies1 lean_a0
    have lean_s6 := R1 (conjunction lean_s2 lean_s4)
    have lean_s9 := notImplies2 lean_s0
    contradiction (conjunction lean_s9 lean_s6)

theorem followsBot : ∀ {t : term},
  followsFrom t bot → ∀ {f : Interpretation}, interpTerm f t = false
  | t, h, f =>
    match r: interpTerm f t with
    | true  => have h' := @h f r
               by simp at h'
    | false => rfl

theorem notMpDEFalse: ∀ {f: Interpretation}, interpTerm f notMpDE = false :=
  followsBot th0
theorem mpDETrue: ∀ {f: Interpretation}, interpTerm f mpDE' = true :=
  interpNotTerm notMpDEFalse

def modusPonens (x y: Bool) : Bool := bimplies x (bimplies (bimplies x y) y)

theorem mp: ∀ {x y: Bool}, modusPonens x y = true 
  | x, y => @mpDETrue λ n => if n == 1000 then x else y

@[simp] def is_equiv (l l₁ l₂: term) := l = xor l₁ l₂

theorem notBneIsEq: ∀ {a b : Bool}, ((a != b) = false) → a = b
  | true, true,   _ => rfl
  | false, false, _ => rfl
  | true, false,  h => by simp at h
  | false, true,  h => by simp at h

theorem eqOfInterps: ∀ (l l₁ l₂: term),
    followsFrom l bot →
    is_equiv l l₁ l₂ →
    ∀ {I : Interpretation}, interpTerm I l₁ = interpTerm I l₂ :=
  by intros l l₁ l₂ h₁ h₂ I
     simp at h₂
     rewrite [h₂] at h₁
     have h₃ := @followsBot (xor l₁ l₂) h₁ I
     simp at h₃
     exact notBneIsEq h₃
