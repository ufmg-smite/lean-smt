import Smt

theorem triv : Nat.zero + Nat.succ Nat.zero = Nat.succ Nat.zero := by
  smt
  simp_all
