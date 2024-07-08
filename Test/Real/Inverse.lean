import Smt
import Smt.Real

theorem inverse (x : Real) : x ≠ 0 → ∃ y, x * y = 1 := by
  smt_show
  sorry
