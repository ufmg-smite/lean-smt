import Smt

theorem refl (p : Bool) : p = p := by
  smt
  simp_all
