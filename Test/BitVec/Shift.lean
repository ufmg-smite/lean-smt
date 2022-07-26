import Smt
import Smt.Data.BitVec

theorem append_eq_shl_or_2 (x y : BitVec 2)
    : x ++ y = (x.zeroExtend 4 (by decide) <<< 2) ||| y.zeroExtend 4 (by decide) := by
  simp only [BitVec.zeroExtend]
  smt
  sorry

theorem append_eq_shl_or_3 (x y : BitVec 3)
    : x ++ y = (x.zeroExtend 6 (by decide) <<< 3) ||| y.zeroExtend 6 (by decide) := by
  simp only [BitVec.zeroExtend]
  smt
  sorry
