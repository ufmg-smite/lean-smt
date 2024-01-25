import Smt

open Std

theorem append_eq_shl_or_2 (x y : BitVec 2)
    : x ++ y = (x.zeroExtend 4 <<< 2) ||| y.zeroExtend 4 := by
  smt_show
  sorry

theorem append_eq_shl_or_3 (x y : BitVec 3)
    : x ++ y = (x.zeroExtend 6 <<< 3) ||| y.zeroExtend 6 := by
  smt_show
  sorry
