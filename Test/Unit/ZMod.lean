import Smt
import Smt.ZMod

open Smt.Reconstruct.ZMod
open MvPolynomial Expr

-- set_option trace.smt true
-- set_option trace.smt.reconstruct.proof true
-- set_option trace.smt.solve true
-- set_option pp.instantiateMVars false

example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
  smt

-- example (a b : ZMod 3) : a*(a-1)*(a-2) + b*(b-1)*(b-2) ≠ 1 := by
--  smt

-- This ends up killing my editor instance.
-- example [Fact (Nat.Prime 394357)] (x1 x2 x3 x4 x5 : ZMod 394357) :
--    ¬ (x1 + x2 + x3 + x4 + x5 = 0 ∧
--     x1*x2 + x2*x3 + x3*x4 + x4*x5 + x5*x1 = 0 ∧
--     x1*x2*x3 + x2*x3*x4 + x3*x4*x5 + x4*x5*x1 + x5*x1*x2 = 0 ∧
--     x1*x2*x3*x4 + x2*x3*x4*x5 + x3*x4*x5*x1 + x4*x5*x1*x2 + x5*x1*x2*x3 = 0 ∧
--      x1*x2*x3*x4*x5 = 1) := by
--  smt

-- This also ends up killing my editor instance...
-- example [Fact (Nat.Prime 7)] (x1 x2 x3 x4 x5 : ZMod 7) :
--    ¬ (x1 + x2 + x3 + x4 + x5 = 0 ∧
--     x1*x2 + x2*x3 + x3*x4 + x4*x5 + x5*x1 = 0 ∧
--     x1*x2*x3 + x2*x3*x4 + x3*x4*x5 + x4*x5*x1 + x5*x1*x2 = 0 ∧
--     x1*x2*x3*x4 + x2*x3*x4*x5 + x3*x4*x5*x1 + x4*x5*x1*x2 + x5*x1*x2*x3 = 0 ∧
--      x1*x2*x3*x4*x5 = 1) := by
--  smt

-- Fails without +native
example [Fact (Nat.Prime 5)] (x y : ZMod 5) : ¬ (x * x = 1 ∧ y * y = 2) := by
  smt

-- Takes too long...
set_option trace.smt true
set_option trace.smt.reconstruct.proof true
set_option trace.smt.solve true
set_option pp.instantiateMVars false
example [Fact (Nat.Prime 5)] (x y : ZMod 5) : ¬ ( y * y = 2 ∧ x * x = 1) := by
  -- smt
  sorry

example [Fact (Nat.Prime 5)] (x: ZMod 5) : x* (x-1)* (x-2) ≠ 1 := by
  smt +model

example (x: ZMod 3) : x + x = 2 * x := by
  smt

example (x: ZMod 3): x + x + x = 0 := by
 smt

example [Fact (Nat.Prime 17)] (x m isz: ZMod 17) : (m*x + 16 + isz = 0 ∧ isz * x = 0) →
      ((isz = 0 ∨ isz = 1) ∧ (isz = 1 ↔ x = 0)) := by
  smt

example [Fact (Nat.Prime 17)] (x: ZMod 17) : -(-x) = x := by
  smt

example [Fact (Nat.Prime 17)] (x: ZMod 17) : x * x ≠ x ∨ x = 1 ∨ x = 0 := by
  smt

open Classical

namespace Test1

-- Overhead is checking if the number is prime
abbrev p := 52435875175126190479447740508185965837690552500527637822603658699938581184513

example [Fact p.Prime] (a b c: Prop) (ret m7 m8 m5 m6 m4 b1 c3 a2: ZMod p) :
       (b1 = (if b then 1 else 0) ∧ c3 = (if c then 1 else 0) ∧ a2 = (if a then 1 else 0)) →
       (b1* (b1 - 1) = 0 ∧ a2 * (a2 - 1) = 0 ∧ c3*(c3 - 1) = 0 ∧
       a2*(-a2 + c3) = m4 ∧ (m4 + a2) * (-b1 + 1) = m5 ∧ m5 * (-m4 - a2 + 1) = m6 ∧
       m6 * (-b1 + 1) = m7 ∧ (-m5 + 1)*(-m7 + 1) = m8 ∧ m8 * (-m7 + 1) = ret) := by
  unfold p at *
  smt +model

end Test1

namespace Test2

abbrev p := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

example [Fact p.Prime] (x: ZMod p) : -(-x) = x := by
 unfold p at *
 smt

example [Fact p.Prime] (x m isz: ZMod p) : ((m * x + isz - 1 = 0) ∧ (isz * x = 0)) ->
  (((isz = 0) ∨ (isz = 1)) ∧ (isz = 1 ↔ x = 0)):= by
 unfold p at *
 smt

end Test2
