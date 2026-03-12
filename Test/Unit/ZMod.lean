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
namespace Smt.Translate.ZMod

open Lean Expr
open Translator Term

-- Focus on ZModExpr instead of ZMods. Use MVPolynomial if ZModExpr is not useful
private def reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
  let some n ← (Meta.evalNat (← Meta.whnf n)).run | throwError "literal{indentD n}\nis not constant in{indentD e}"
  return n

private def reduceZModOrder? (e : Expr) : MetaM (Option Nat) := do
  let some (order, ring) := e.app2? ``MvPolynomial | return none
  let some o := ring.app1? ``ZMod | return none

  let some o' ← (Meta.evalNat o).run | throwError "zmod type{indentD e}\nhas variable order"
  if o'.minFac != o' then
    throwError "zmod order{indentD o}\nis not a prime in{indentD e}"
  return o'

@[smt_translate] def translateType : Translator := fun e => do
  if let some o ← reduceZModOrder? e then
    return mkApp2 (symbolT "_") (symbolT "FiniteField") (literalT (toString o))
  else
    return none

-- Modify to work with ZmodExpr instead of ZMod
@[smt_translate] def translateZMod : Translator := fun e => do match_expr e with
  | OfNat.ofNat α n _ =>
    ---let some _ ← reduceZModOrder? α | return none
    let n ← reduceLit n e
    return some (mkApp2 (symbolT "as") (literalT s!"ff{n}") (← applyTranslators! α))
  | Neg.neg α _ x =>
    let some _ ← reduceZModOrder? α | return none
    return some (appT (symbolT "ff.neg") (← applyTranslators! x))
  | HAdd.hAdd α β _ _ x y =>
    let some _ ← reduceZModOrder? α | return none
    let some _ ← reduceZModOrder? β | return none
    return some (mkApp2 (symbolT "ff.add") (← applyTranslators! x) (← applyTranslators! y))
  | HMul.hMul α β _ _ x y =>
    let some _ ← reduceZModOrder? α | return none
    let some _ ← reduceZModOrder? β | return none
    return some (mkApp2 (symbolT "ff.mul") (← applyTranslators! x) (← applyTranslators! y))
  | MvPolynomial.C _ _ _ c =>
    return some (<- applyTranslators! c)
  -- | MvPolynomial.X _ _ _ _ x =>
  --   --let n := x.natLit! | return none


  | _                  => return none
end Smt.Translate.ZMod

abbrev R (n : ℕ) := ZMod n
abbrev P (n : ℕ) (σ : Type u) := MvPolynomial σ (R n)

/-- Expressions over variables `σ` with coefficients in `ZMod n`. -/
inductive ZModExpr (n : ℕ) (σ : Type u) : Type u
| var   : σ → ZModExpr n σ
| const : R n → ZModExpr n σ
| add   : ZModExpr n σ → ZModExpr n σ → ZModExpr n σ
| mul   : ZModExpr n σ → ZModExpr n σ → ZModExpr n σ
| neg   : ZModExpr n σ → ZModExpr n σ
| pow   : ZModExpr n σ → ℕ → ZModExpr n σ

namespace ZModExpr

def toZMod (f: σ → ZMod n)(p: ZModExpr n σ) : ZMod n :=
  match p with
  | .var i     => f i
  | .const c   => c
  | .add a b   => toZMod f a + toZMod f b
  | .mul a b   => toZMod f a * toZMod f b
  | .neg a     =>  -(toZMod f a)
  | .pow a k   => (toZMod f a) ^ k


noncomputable section

def toPoly {n : ℕ} {σ : Type u} : ZModExpr n σ → P n σ
| .var i     => MvPolynomial.X i
| .const c   => MvPolynomial.C c
| .add a b   => toPoly a + toPoly b
| .mul a b   => toPoly a * toPoly b
| .neg a     =>  MvPolynomial.C (-1) * toPoly a
| .pow a k   => (toPoly a) ^ k
end
end ZModExpr

--set_option pp.all true
-- example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
--   smt

example (x: MvPolynomial Nat (ZMod 5)) : (3 :MvPolynomial Nat (ZMod 5)) = 3 := by
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

def toMVPoly (σ) (x: ZMod n) : MvPolynomial σ (ZMod n) := MvPolynomial.C x

def toZModExpr (σ) (x: ZMod n) : ZModExpr n σ := ZModExpr.const x

-- Figure out what are the theorems that we want to prove in this conversion. (either aeval or something equivalent).
example (x y: ZMod n) : x = y ↔ toMVPoly σ x = toMVPoly σ y := by
  simp [toMVPoly]

example (x y: ZMod n) : x ≠ y ↔ toMVPoly σ x ≠ toMVPoly σ y := by
  simp [toMVPoly]

example : toMVPoly (ZMod 0) (3: ZMod 5)  = MvPolynomial.C (3) := by
  simp [toMVPoly]

example : toMVPoly (ZMod 0) (3 + 4 : ZMod 5)  = MvPolynomial.C (3) + MvPolynomial.C 4 := by
  simp [toMVPoly]

example (x y: ZMod 5): toMVPoly (ZMod 0) (x + y : ZMod 5) = MvPolynomial.C x + MvPolynomial.C y := by
  simp_all [toMVPoly]
  sorry
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
variable [CommSemiring S₂] [CommSemiring R] [CommSemiring S₁]  [Algebra R S₁]

variable (f : σ → S₁)

theorem aeval_X (s : σ) : MvPolynomial.aeval f (MvPolynomial.X s : MvPolynomial σ R) = f s := by
  simp

theorem aeval_C (r : R) : MvPolynomial.aeval f (MvPolynomial.C r) = algebraMap R S₁ r := by
  simp

variable [CommSemiring S₂] [CommSemiring R] [CommSemiring S₁]  [Algebra R R]

variable (f : σ → R)

example (s: σ) (r: R): MvPolynomial.aeval f (MvPolynomial.C r) = MvPolynomial.aeval f (MvPolynomial.X s : MvPolynomial σ R) := by
  simp
  have hrr: (algebraMap R R) r = id r := by sorry
  simp [hrr]
  sorry

-- This is false
example (s: σ) (r: R):  (MvPolynomial.C r) = (MvPolynomial.X s : MvPolynomial σ R) := by
  sorry

-- σ = Fin n -> n is the number of variables
-- R = ZMod p -> p is the prime order
-- r = ZMod p var (x, y, ...)
-- s = index of vars x, y, ...
-- f = {s ↦ r}
-- 1st question: Are we able to prove the above theorem with this assumptions
-- 2nd question: Does this transformation preserve the semantics of the proof rules
-- Can we actually pick such f (looks like it).
