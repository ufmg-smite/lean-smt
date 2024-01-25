import Smt

theorem inverse (x : Rat) : x ≠ 0 → ∃ y, x * y = 1 := by
  smt_show
  sorry
