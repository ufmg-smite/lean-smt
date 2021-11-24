import Smt

theorem disjunctive_syllogism (p q : Prop) : p ∨ q → ¬p → q := by
  smt
  intro hpq hnp
  simp_all
