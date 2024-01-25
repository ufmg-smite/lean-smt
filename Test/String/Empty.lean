import Smt

theorem empty : "" = "" := by
  smt_show
  rfl
