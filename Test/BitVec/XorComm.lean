import Smt
open Std BitVec

theorem xor_comm_2 (x y : BitVec 2) : x ^^^ y = y ^^^ x  := by
  smt
  sorry

theorem xor_comm_4p4 (x y : BitVec (4+4)) : x ^^^ y = y ^^^ x  := by
  smt
  sorry
