import Smt
import Smt.Real

/- example : True := by smt -/

/- example (a : Real) : a < 2 → a < 2 := by smt -/

/- set_option maxRecDepth 10000000 -/
/- set_option maxHeartbeats 10000000 -/
/- lemma l1 (a : Real) : a * a = 3 → a * a * a + 11 < 2 → False := by smt -/

/- #print axioms l1 -/

/- lemma l2 (a : Real) : a * a = 3 → a * a * a + 11 < 2 → False := by nlinarith -/

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000
lemma l (a : Real) : a > 3 / 2 → a * a + a / 5 = 3 / 2 → False := by
  smt

#print axioms l
