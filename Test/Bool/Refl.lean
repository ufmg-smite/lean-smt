import Smt

theorem refl (p : Bool) : p == p := by
  smt
  cases p <;> simp_all
