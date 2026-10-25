import Smt

-- Euclidean mod with a variable divisor. Exercises ARITH_MULT_ABS_COMPARISON
-- with an AND-shaped premise and ARITH_REDUCTION of mod/mod_total.
example (v m : Int) (h1 : 0 ≤ v) (h2 : v < m) : v % m = v := by
  smt [h1, h2]

-- Divisibility (in existential form) bounds the divisor.
example (c d : Int) (h1 : ∃ k, d = c * k) (h2 : 0 < d) : c ≤ d := by
  smt [h1, h2]
