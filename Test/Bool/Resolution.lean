import Smt

theorem resolution (p q r : Bool) : p || q → !p || r → q || r := by
  smt
  intro hpq
  intro hnpr
  cases p <;> cases r <;> simp_all
