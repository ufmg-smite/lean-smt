import Smt

theorem modus_tollens (p q : Bool) : !q → (p → q) → !p := by
  smt
  intro hnq hpq
  cases p <;> simp_all
