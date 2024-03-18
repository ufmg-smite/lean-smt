import Smt

theorem triv'' (p : Bool) : !p → !p := by
  smt_show
  simp_all
