import Smt

theorem cong (p q : Bool) (f : Bool → Bool) : p == q → f p == f q := by
  smt
  cases p <;> cases q <;> cases f true <;> cases f false <;> simp_all
