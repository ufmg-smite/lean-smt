import Smt
import Smt.Real

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

lemma l1 (a : Real) : a * a = 3 → a * a * a + 11 < 2 → False := by smt

#print axioms l1

lemma l2 (a : Real) : a > 3 / 2 → a * a + a / 5 = 3 / 2 → False := by
  smt

#print axioms l2

lemma ex1 (x : Real) : (¬ (x ≥ -9 ∧ x < 10 ∧ x * x * x * x > 0) ∨ (x * x * x * x * x * x * x * x * x * x * x * x > 0)) := by
  smt

#print axioms ex1
