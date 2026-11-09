import Smt
import Smt.Real

-- cvc5's integer division lemmas give ARITH_TRICHOTOMY premises such as `¬(x < c)` and
-- `¬(x = c)`, not just `x ≥ c` and `x ≠ c`.

example (i : Int) (h₁ : 16 ≤ i) (h₂ : i < 32) : i / 16 = 1 := by
  smt [h₁, h₂]
