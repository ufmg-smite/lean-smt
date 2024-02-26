import Smt

theorem neg (x : Int) : - -x = x := by
  smt_show <;> sorry
