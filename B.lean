import Smt
import Smt.Real

-- v1 (7211561): 3372ms
-- v2 (b81b158): 3009ms
lemma exemplo (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by
  revert h1 h2
  smt

#print axioms exemplo

-- v1 (7211561): 3810ms
-- v2 (b81b158): 3287ms
lemma l1 (a : Real) : a * a = 3 → a * a * a + 11 < 2 → False := by smt

#print axioms l1

-- v1 (7211561): 2244ms
-- v2 (b81b158): 2275ms
lemma ex1 (x : Real) : (¬ (x ≥ -9 ∧ x < 10 ∧ x * x * x * x > 0) ∨ (x * x * x * x * x * x * x * x * x * x * x * x > 0)) := by
  smt

#print axioms ex1

-- v1 (7211561): 9079ms
-- v2 (b81b158): 9051ms
lemma ex2 (x : Real) :
    ¬ ((x - 2) * (x - 2) * (-x + 4) > 0 ∧ x * x * (x - 3) * (x - 3) ≥ 0 ∧ x - 1 ≥ 0 ∧ -(x - 2) * (x - 2) + 1 > 0)
    ∨ (-(x - 11/12)) * (-(x - 11/12)) * (-(x - 11/12)) * (x - 41/10) * (x - 41/10) * (x - 41/10) ≥ 0 := by
  smt

#print axioms ex2

/- set_option trace.smt true -/
/- set_option trace.smt.reconstruct true -/
/- set_option trace.smt.reconstruct.proof true -/
-- polynorm is proving this - can we disable it?
/- lemma ex4 (x : Real) : x > 0 ∨ (20 / 9) * x * x * x + 5 / 9 * x * x - 61 / 9 * x > -4 ∨ 1 ≤ x ∨ x ≤ 0 ∨ 10/9 * x * x - 19/9 * x ≤ -1 ∨ -/
/-     1/18 * x * x * x + 31 / 45 * x * x - 13 / 9 * x ≤ -8/10 ∨ 20/3 * x * x * x + 5/9 * x * x - 61 / 9 * x ≤ -4 := by -/
/-   smt -/

/- #print axioms ex4 -/

/- lemma ex5 (x : Real) : - x * x * x / 3 - 10/3 * x * x - 5 / 6 * x > 0 -/
