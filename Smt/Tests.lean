import Smt.Tactics

theorem tri: ∀ (p : Prop), ∀ _ : p, p := by
  check_sat
  intro p
  simp_all

theorem triv (p : Prop) : p → p := by
  check_sat
  simp_all

theorem triv' (p : Prop) : ¬p → ¬p := by
  check_sat
  simp_all



theorem verum : True := by
  check_sat
  simp_all

theorem not_falsum : ¬False := by
  check_sat
  simp_all

theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  check_sat
  simp_all

theorem modus_tollens (p q : Prop) : ¬q → (p → q) → ¬p := by
  check_sat
  intro hnq hpq hp
  simp_all

theorem hypothetical_syllogism (p q r : Prop) : (p → q) → (q → r) → p → r := by
  check_sat
  simp_all

theorem disjunctive_syllogism (p q : Prop) : p ∨ q → ¬p → q := by
  check_sat
  intro hpq hnp
  simp_all

theorem addition (p q : Prop) : p → p ∨ q := by
  check_sat
  simp_all

theorem simplification (p q : Prop) : p ∧ q → p := by
  check_sat
  simp_all

theorem conjunction (p q : Prop) : p → q → p ∧ q := by
  check_sat
  simp_all

theorem resolution (p q r : Prop) : p ∨ q → ¬p ∨ r → q ∨ r := by
  check_sat
  intro hpq hnpr
  induction hpq <;> simp_all

theorem test : ∃ (p : Prop), p := by
  check_sat
  exact Exists.intro True True.intro

theorem prop_ext (p q : Prop) : (p ↔ q) -> p = q := by
  check_sat
  simp_all

-- UF Axioms (apply to all sorts, not just Prop)

theorem refl (p : Prop) : p = p := by
  check_sat
  simp_all

theorem symm (p q : Prop) : p = q → q = p := by
  check_sat
  simp_all

theorem trans (p q r : Prop) : p = q → q = r → p = r := by
  check_sat
  simp_all

theorem cong (p q : Prop) (f : Prop → Prop) : p = q → f p = f q := by
  check_sat
  simp_all


-- LIA

theorem lia1 : Nat.zero + Nat.succ Nat.zero = Nat.succ Nat.zero := by
  check_sat
  simp_all
