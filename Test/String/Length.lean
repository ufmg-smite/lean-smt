import Smt

theorem length : "a".length = 1 := by
  smt_show -embeddings
  rfl
