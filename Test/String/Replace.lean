import Smt

theorem replace : "a".replace "a" "b" = "b" := by
  smt_show
  admit
