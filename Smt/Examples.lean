import Smt.Tactics

theorem modus_ponens' (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
  simp_all

theorem verum : True := by
  smt
  simp_all

theorem falsum : ¬False := by
  smt
  simp_all

theorem triv (p : Prop) : p → p := by
  smt
  simp_all

theorem triv': ∀ (p : Prop), ∀ _ : p, p := by
  smt
  intro p
  simp_all

#check triv
#check triv'

theorem triv'' (p : Prop) : ¬p → ¬p := by
  smt
  simp_all

theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  smt
  simp_all

theorem modus_ponens' (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp,]
  simp_all

theorem modus_tollens (p q : Prop) : ¬q → (p → q) → ¬p := by
  smt
  intro hnq hpq hp
  simp_all
  

theorem hypothetical_syllogism (p q r : Prop) : (p → q) → (q → r) → p → r := by
  smt
  simp_all

theorem disjunctive_syllogism (p q : Prop) : p ∨ q → ¬p → q := by
  smt
  intro hpq hnp
  simp_all

theorem addition (p q : Prop) : p → p ∨ q := by
  smt
  simp_all

theorem simplification (p q : Prop) : p ∧ q → p := by
  smt
  simp_all

theorem conjunction (p q : Prop) : p → q → p ∧ q := by
  smt
  simp_all

theorem resolution (p q r : Prop) : p ∨ q → ¬p ∨ r → q ∨ r := by
  intro hpq
  intro hnpr
  smt
  induction hpq <;> simp_all

theorem prop_ext (p q : Prop) : (p ↔ q) → p = q := by
  smt
  simp_all

-- UF Axioms (apply to all sorts, not just Prop)

theorem refl (p : Prop) : p = p := by
  smt
  simp_all

theorem symm (p q : Prop) : p = q → q = p := by
  smt
  simp_all

theorem trans (p q r : Prop) : p = q → q = r → p = r := by
  smt
  simp_all

theorem cong (p q : Prop) (f : Prop → Prop) : p = q → f p = f q := by
  smt
  simp_all


theorem comm (f : Prop → Prop → Prop) (p q : Prop) : f p q = f q p := by
  smt
  admit

theorem assoc (f : Prop → Prop → Prop) (p q r : Prop) : f p (f q r) = f (f p q) r := by
  smt
  admit

-- LIA

theorem lia1 : Nat.zero + Nat.succ Nat.zero = Nat.succ Nat.zero := by
  smt
  simp_all

theorem lia1' : 0 + 1 = 1 := by
  smt
  simp_all

theorem lia2 (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  smt
  simp_all

-- Progress
theorem lia3 : 1 - 3 = 0 := by
  smt
  simp_all

/-
(declare-const x Int)
(assert (>= x 0))
(define-fun minus ((x Int) (y Int)) Int (ite (< x y) 0 (- x y)))
(assert (= (minus 1 3) 0))
; ∀ x, Math.min 0 x = 0
(assert (forall (x Int) (=> (x >= 0) (= (min 0 x) 0))))
(check-sat)
-/

#eval 1 - 3

theorem test : ∃ (p : Prop), p := by
  smt
  exact Exists.intro True True.intro

theorem test2 (p q : Prop) (hp : p) (f : p → q) : q := by
  smt [hp, f]
  exact f hp
