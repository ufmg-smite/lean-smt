import Smt

theorem refl (p : Prop) : p = p := by
  smt
  simp_all
