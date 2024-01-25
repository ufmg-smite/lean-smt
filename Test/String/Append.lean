import Smt

theorem append : "a" ++ "b" = "ab" := by
  smt_show
  rfl
