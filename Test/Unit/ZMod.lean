import Smt
import Smt.ZMod
import Mathlib.Data.ZMod.Basic

set_option trace.smt true
set_option trace.smt.reconstruct.proof true
set_option trace.smt.solve true

example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
  smt +trust

example (x: ZMod 3) : x + x = 2 * x := by
  smt +trust

example (x: ZMod 3): x + x + x = 0 := by
  smt +trust

example (x m isz: ZMod 17): (m*x + 16 + isz = 0 ∧ isz * x = 0) →
        ((isz = 0 ∨ isz = 1) ∧ (isz = 1 ↔ x = 0)) := by
  smt +trust

example (x: ZMod 17): -(-x) = x := by
  smt +trust

example (x: ZMod 17): x * x ≠ x ∨ x = 1 ∨ x = 0 := by
  smt +trust

-- Overhead is checking if the number is prime
--abbrev zp := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- #eval Nat.minFac 52435875175126190479447740508185965837690552500527637822603658699938581184513
--
--example (a b c: Bool) (ret m7 m8 m5 m6 m4 b1 c3 a2: zp) :
--        (b1 = (if b then 1 else 0) ∧ c3 = (if c then 1 else 0) ∧ a2 = (if a then 1 else 0)) →
--        (b1* (b1 - 1) = 0 ∧ a2 * (a2 - 1) = 0 ∧ c3*(c3 - 1) = 0 ∧
--        a2*(-a2 + c3) = m4 ∧ (m4 + a2) * (-b1 + 1) = m5 ∧ m5 * (-m4 - a2 + 1) = m6 ∧
--        m6 * (-b1 + 1) = m7 ∧ (-m5 + 1)*(-m7 + 1) = m8 ∧ m8 * (-m7 + 1) = ret) := by
--  unfold zp at *
--  smt +trust
--  sorry
--abbrev zz := ZMod 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
--#eval Nat.minFac 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
--example (x: zz): -(-x) = x := by
--  unfold zz at x
--  smt +trust
--  sorry
-- 
---- example (x m isz: zz): ((m * x + isz - 1 = 0) ∧ (isz * x = 0)) ->
--         (((isz = 0) ∨ (isz = 1)) ∧ (isz = 1 ↔ x = 0)):= by
--  unfold zz at x m isz
--  smt +trust
--  sorry


