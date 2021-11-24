import Smt

theorem modus_tollens (p q : Prop) : ¬q → (p → q) → ¬p := by
  smt
  intro hnq hpq hp
  simp_all
