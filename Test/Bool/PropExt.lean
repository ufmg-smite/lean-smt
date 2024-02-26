import Smt

theorem prop_ext (p q : Bool) : (p ↔ q) → p == q := by
  smt_show
  intro ⟨hpq, hqp⟩
  cases p <;> cases q <;> simp_all
