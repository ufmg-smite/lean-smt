import Smt
import Smt.Real

set_option trace.smt true
set_option trace.smt.reconstruct.proof true
set_option trace.smt.solve true



example (a : Real) : a > 3 / 2 → a * a + a / 5 = 3 / 2 → False := by smt
