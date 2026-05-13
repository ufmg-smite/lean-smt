import Smt
import Smt.Real

-- v1: 3372ms
-- v2: 3009ms
-- v3: 1007ms
lemma exemplo (a : Real) : ¬ -1 * a ≥ -3 / 2 → a = 15 / 2 + -5 * (a * a) → False := by
  smt

#print axioms exemplo

-- v1: 3810ms
-- v2: 3287ms
-- v3: 1084ms
lemma l1 (a : Real) : a * a = 3 → a * a * a + 11 < 2 → False := by
  smt

#print axioms l1

-- v1 (7211561): 2244ms
-- v2 (b81b158): 2275ms
-- v3 (bfea4e7): 1093ms
lemma ex1 (x : Real) : (¬ (x ≥ -9 ∧ x < 10 ∧ x * x * x * x > 0) ∨ (x * x * x * x * x * x * x * x * x * x * x * x > 0)) := by
  smt

#print axioms ex1

-- v1: 9079ms
-- v2: 9051ms
-- v3: 2936ms
lemma ex2 (x : Real) :
    ¬ ((x - 2) * (x - 2) * (-x + 4) > 0 ∧ x * x * (x - 3) * (x - 3) ≥ 0 ∧ x - 1 ≥ 0 ∧ -(x - 2) * (x - 2) + 1 > 0)
    ∨ (-(x - 11/12)) * (-(x - 11/12)) * (-(x - 11/12)) * (x - 41/10) * (x - 41/10) * (x - 41/10) ≥ 0 := by
  smt +native

#print axioms ex2
