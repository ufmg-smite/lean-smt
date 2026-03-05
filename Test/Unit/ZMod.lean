import Smt
import Smt.ZMod
import Smt.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Field.Defs

set_option trace.smt true
set_option trace.smt.reconstruct.proof true
set_option trace.smt.solve true

example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
  smt

example (x: ZMod 3) : x + x = 2 * x := by
  smt +trust

example (x: ZMod 3): x + x + x = 0 := by
  smt +trust

example (x m isz: ZMod 17): (m*x + 16 + isz = 0 ∧ isz * x = 0) →
        ((isz = 0 ∨ isz = 1) ∧ (isz = 1 ↔ x = 0)) := by
  smt +trust

example (x: ZMod 17): -(-x) = x := by
  smt 

example (x: ZMod 17): x * x ≠ x ∨ x = 1 ∨ x = 0 := by
  smt 

example (x y: MvPolynomial (Fin 3) (ZMod 17)) : 3 * x + y = y + x + x + x := by
  grind


local instance : Fact (Nat.Prime 7) := ⟨by decide⟩ -- “field coefficients”: ZMod n is a field when n is prime

-- define a type class if n is prime then ZMod n is a field 
instance test_prime (h: Nat.Prime n): Field (ZMod n) := sorry


abbrev K : Type := ZMod 7
abbrev σ := Fin 2


-- convention: 0 ↦ x, 1 ↦ y
def α (x y : K) : σ → K
| 0 => x
| 1 => y

abbrev Poly := MvPolynomial σ K
#check Ideal (MvPolynomial σ K)

abbrev help : CommSemiring (ZMod 7) := (@Field.toSemifield _ (test_prime sorry)).toCommSemiring

abbrev help2 : Semiring (ZMod 7) := (@Field.toSemifield _ (test_prime sorry)).toSemiring


noncomputable section 
/-- The polynomial corresponding to (x + y) -/
def poly_xy : @MvPolynomial σ (ZMod 7) help:= @MvPolynomial.C _ _ help 3 * @MvPolynomial.X _ _ help  (0 : σ) + @MvPolynomial.X  _ _ help (1 : σ)

example  MvPolynomial.C 3 + MvPolynomial.C 5 = MvPolynomial.C 8 :=  by 
  grind

def V : Set (σ → K) :=
  @MvPolynomial.zeroLocus (σ := σ) (ZMod 7) (ZMod 7) (test_prime sorry) (test_prime sorry) _ (Ideal.span ({poly_xy} : Set (@MvPolynomial σ (ZMod 7) (@Field.toSemifield _ (test_prime sorry)).toCommSemiring)))

def variety (I : Ideal Poly) : Set (σ → K) :=
  {a | ∀ f ∈ I, MvPolynomial.aeval a f = 0}

variable {p : ℕ} [Fact p.Prime]

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
#check (inferInstance : Field (ZMod p))
#check (inferInstance : Field K)
-- Overhead is checking if the number is prime
abbrev zp := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513

-- example : Nat.minFac 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 := by
--   native_decide


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


