import Smt

theorem lt : "a" < "b" := by
  smt_show
  decide
