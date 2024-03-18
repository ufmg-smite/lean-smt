import Smt

theorem disjunctive_syllogism (p q : Bool) : p || q → !p → q := by
  smt_show
  intro hpq hnp
  cases p <;> simp_all
