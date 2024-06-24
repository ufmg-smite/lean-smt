import Smt
import Smt.Real

theorem density (x z : Real) : x < z → ∃ y, x < y ∧ y < z := by
  smt_show
  sorry
