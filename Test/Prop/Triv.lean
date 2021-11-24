import Smt

theorem triv (p : Prop) : p → p := by
  smt
  simp_all
