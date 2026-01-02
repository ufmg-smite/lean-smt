import Smt

theorem index : String.Pos.Raw.get! "a" 0 = 'a' := by
  smt_show
  rfl
