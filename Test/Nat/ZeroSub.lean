import Smt

theorem zero_sub : 0 - x = 0 := by
  smt
  induction x <;> simp_all [Nat.sub_succ]
