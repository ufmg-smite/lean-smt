import Smt

theorem triv'' (p : Bool) : !p → !p := by
  smt
  simp_all
