import Smt

theorem modus_tollens (p q : Prop) : ¬q → (p → q) → ¬p := by
  smt
