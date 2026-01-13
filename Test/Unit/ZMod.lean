import Smt
import Smt.ZMod

set_option trace.smt true
set_option trace.smt.solve true
-- example (x: ZMod 3) : x + x = 2 * x := by
--   smt +trust
