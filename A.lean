import Smt
import Smt.Real
set_option trace.smt true in
set_option trace.smt.reconstruct true in
set_option trace.smt.reconstruct.proof true in
example (a : Real) : a > 3 / 2 → a * a + a / 5 = 3 / 2 → False := by
  smt
