import Smt
open Std BitVec

theorem append_eq_shl_or_2 (x y : BitVec 2)
    : x ++ y = (x.zeroExtend 2 <<< 2) ||| y.zeroExtend 2 := by
  smt
  sorry

theorem append_eq_shl_or_3 (x y : BitVec 3)
    : x ++ y = (x.zeroExtend 3 <<< 3) ||| y.zeroExtend 3 := by
  smt
  sorry
