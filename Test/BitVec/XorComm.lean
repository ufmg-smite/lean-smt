import Smt
import Smt.Data.BitVec

theorem xor_comm_2 (x y : BitVec 2) : x ^^^ y = y ^^^ x  := by
  smt -- TODO: x, y are not emitted
  sorry

theorem xor_comm_8 (x y : BitVec 8) : x ^^^ y = y ^^^ x  := by
  smt
  sorry
