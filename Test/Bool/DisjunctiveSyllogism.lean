import Smt

theorem disjunctive_syllogism (p q : Bool) : p || q → !p → q := by
  smt
