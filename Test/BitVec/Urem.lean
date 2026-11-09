import Smt

example (b : BitVec 32) : b % 8#32 = b % 8#32 := by
  smt

theorem urem_show (x y : BitVec 8) : x % y = x % y := by
  smt_show
  sorry
