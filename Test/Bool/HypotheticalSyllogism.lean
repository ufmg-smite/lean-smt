import Smt

theorem hypothetical_syllogism (p q r : Bool) : (p → q) → (q → r) → p → r := by
  smt
  simp_all
