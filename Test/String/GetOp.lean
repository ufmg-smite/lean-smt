import Smt

theorem index : "a".get 0 = 'a' := by
  smt_show
  rfl
