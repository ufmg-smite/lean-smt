import Smt
import Smt.ZMod
import Smt.Reconstruct.ZMod.Polynorm
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
open Qq
open Translator Term
open Smt
open Reconstruct

-- Focus on ZModExpr instead of ZMods. Use MVPolynomial if ZModExpr is not useful
private def reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
  let some n ← (Meta.evalNat (← Meta.whnf n)).run | throwError "literal{indentD n}\nis not constant in{indentD e}"
  return n

private def reduceZModOrder? (e : Expr) : MetaM (Option Nat) := do
  let some o := e.app1? ``ZMod | return none
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
    let some _ ← reduceZModOrder? α | return none
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
  | _                  => return none
end Smt.Translate.ZMod

-- abbrev R (n : ℕ) := ZMod n
-- abbrev P (n : ℕ) (σ : Type u) := MvPolynomial σ (R n)

/-- Expressions over variables `σ` with coefficients in `ZMod n`. -/
inductive ZModExpr (n : ℕ) where
| var   : ℕ → ZModExpr n
| const : ZMod n → ZModExpr n
| add   : ZModExpr n  → ZModExpr n  → ZModExpr n
| mul   : ZModExpr n  → ZModExpr n  → ZModExpr n
| neg   : ZModExpr n  → ZModExpr n
| pow   : ZModExpr n  → ℕ → ZModExpr n

namespace ZModExpr

def toZMod (ctx: ℕ → ZMod n)(p: ZModExpr n) : ZMod n :=
  match p with
  | .var i     => ctx i
  | .const c   => c
  | .add a b   => toZMod ctx a + toZMod ctx b
  | .mul a b   => toZMod ctx a * toZMod ctx b
  | .neg a     =>  -(toZMod ctx a)
  | .pow a k   => (toZMod ctx a) ^ k


noncomputable section

--- TODO CHANG FROM FIELD TO PRIME
instance test_prime (h: Nat.Prime n): Field (ZMod n) := sorry

-- TODO PROVE THIS THEOREM
theorem field_toCommSemiring_eq_commRing_toCommSemiring
    (R : Type*) [Field R] :
    (Field.toSemifield.toCommSemiring : CommSemiring R) =
    (CommRing.toCommSemiring : CommSemiring R) := sorry


def toPoly {n : ℕ} [Field (ZMod n)] : ZModExpr n → MvPolynomial ℕ (ZMod n) := by
  letI : CommSemiring (ZMod n) := Field.toSemifield.toCommSemiring
  intro p
  induction p with
  | var i =>
      exact MvPolynomial.X i
  | const c =>
      exact MvPolynomial.C c
  | add a b ia ib =>
      exact ia + ib
  | mul a b ia ib =>
      exact ia * ib
  | neg a ia =>
      exact MvPolynomial.C (-1) * ia
  | pow a k ia =>
      exact ia ^ k



def ideal {n : ℕ} [Field (ZMod n)] (s : Set (ZModExpr n)) : Ideal (MvPolynomial ℕ (ZMod n) ) :=
  Ideal.span (ZModExpr.toPoly '' s)

def variety {n : ℕ} [Field (ZMod n)] (s : Set (ZModExpr n)) : Set (ℕ → ZMod n) :=
  MvPolynomial.zeroLocus (ZMod n) (ideal s)

end
end ZModExpr



namespace Smt.Reconstruct.ZMod
open Lean
open Qq
@[smt_sort_reconstruct] def reconstructZModSort : SortReconstructor := fun s => do match s.getKind with
  | .FINITE_FIELD_SORT =>
    let o : Nat := s.getFiniteFieldSize!
    return q(ZMod  $o)
  | _             => return none

  @[smt_term_reconstruct] def reconstructZMod : TermReconstructor := fun t => do match t.getKind with
  | .CONST_FINITE_FIELD =>
    let o : Nat := t.getSort.getFiniteFieldSize!
    let v : Nat := (t.getFiniteFieldValue!.toInt! % o).toNat
    return mkZModLit o v
  | .FINITE_FIELD_ADD =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    leftAssocOp q(@HAdd.hAdd (ZMod $w) (ZMod $w) (ZMod $w) _) t
  | .FINITE_FIELD_MULT =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    leftAssocOp q(@HMul.hMul (ZMod $w) (ZMod $w) (ZMod $w) _) t
  | .FINITE_FIELD_NEG =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    let x : Q(ZMod $w) ← reconstructTerm t[0]!
    return q(-$x)
  | .FINITE_FIELD_VARIETY =>
    let o:  Nat := t.getSort.getSetElementSort!.getFiniteFieldSize!
    let s : Q(Set (_root_.ZModExpr $o))  ← reconstructTerm (t[0]!)[0]!
    return q(@ZModExpr.variety $o sorry $s)
  | .FINITE_FIELD_IDEAL =>
    let o:  Nat := t.getSort.getSetElementSort!.getFiniteFieldSize!
    let s : Q(Set (_root_.ZModExpr $o))  ← reconstructTerm t[0]!
    return q(@ZModExpr.ideal $o sorry $s)
  | .SET_MEMBER =>
    let o:  Nat := t[0]!.getSort.getSetElementSort!.getFiniteFieldSize!
    let p:  Q(ZMod $o)  ← reconstructTerm t[0]!
    let pExpr
    let s:  Q(Set (_root_.ZModExpr $o))  ← reconstructTerm t[1]!

  | _ => return none
where
  mkZModLit  (o: Nat) (n : Nat): Q(ZMod $o) := match n with
    | 0     => q(0 : ZMod $o)
    | 1     => q(1 : ZMod $o)
    | n' + 1 + 1 =>
      let h : Q(Nat.AtLeastTwo $n) := mkApp2 q(@Nat.instAtLeastTwoHAddOfNat) (toExpr (n' + 1)) q(@Nat.instNeZeroSucc $n')
      let h := mkApp3 q(@instOfNatAtLeastTwo (ZMod $o)) (mkRawNatLit n) q((ZMod.commRing $o).toAddGroupWithOne.toNatCast) h
      mkApp2 q(@OfNat.ofNat (ZMod $o)) (mkRawNatLit n) h
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr


def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
--  | .ARITH_POW_ELIM =>
--    if !pf.getResult[0]![0]!.getSort.isInteger then return none
--    let x : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
--    let c : Q(Nat) ← reconstructTerm pf.getResult[0]![1]!
--    let y : Q(Int) ← reconstructTerm pf.getResult[1]!
--    addThm q($x ^ $c = $y) q(Eq.refl ($x ^ $c))
  | _ => return none

--  def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
--   let cx : Int := pf.getChildren[0]!.getResult[0]![0]!.getIntegerValue!
--   let cy : Int := pf.getChildren[0]!.getResult[1]![0]!.getIntegerValue!
--   let x₁ : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
--   let x₂ : Q(Int) ← reconstructTerm pf.getResult[0]![1]!
--   let y₁ : Q(Int) ← reconstructTerm pf.getResult[1]![0]!
--   let y₂ : Q(Int) ← reconstructTerm pf.getResult[1]![1]!
--   let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructProof pf.getChildren[0]!
--   let k := pf.getResult[0]!.getKind
--   let (hcx, hcy) :=
--     if k == .EQUAL then (q(@of_decide_eq_true ($cx ≠ 0) _), q(@of_decide_eq_true ($cy ≠ 0) _))
--     else if cx > 0 then (q(@of_decide_eq_true ($cx > 0) _), q(@of_decide_eq_true ($cy > 0) _))
--     else (q(@of_decide_eq_true ($cx < 0) _), q(@of_decide_eq_true ($cy < 0) _))
--   let hcx := .app hcx q(Eq.refl true)
--   let hcy := .app hcy q(Eq.refl true)
--   let n ← getThmName k (cx > 0)
--   return mkApp9 (.const n []) x₁ x₂ y₁ y₂ q($cx) q($cy) hcx hcy h
-- where
--   getThmName (k : cvc5.Kind) (sign : Bool) : ReconstructM Name :=
--     if k == .LT && sign == true then pure ``Int.lt_of_sub_eq_pos
--     else if k == .LT && sign == false then pure ``Int.lt_of_sub_eq_neg
--     else if k == .LEQ && sign == true then pure ``Int.le_of_sub_eq_pos
--     else if k == .LEQ && sign == false then pure ``Int.le_of_sub_eq_neg
--     else if k == .EQUAL then pure ``Int.eq_of_sub_eq
--     else if k == .GEQ && sign == true then pure ``Int.ge_of_sub_eq_pos
--     else if k == .GEQ && sign == false then pure ``Int.ge_of_sub_eq_neg
--     else if k == .GT && sign == true then pure ``Int.gt_of_sub_eq_pos
--     else if k == .GT && sign == false then pure ``Int.gt_of_sub_eq_neg
--     else throwError "[arith_poly_norm_rel]: invalid combination of kind and sign: {k}, {sign}"

open Qq

@[smt_proof_reconstruct] def reconstructFfProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .FF_POLY_NORM =>
    if !pf.getResult[0]!.getSort.isFiniteField then return none
    logInfo "here"
    let o : Nat := pf.getResult[0]!.getSort.getFiniteFieldSize!
    logInfo "here1"
    let a : Q(ZMod $o) ← reconstructTerm pf.getResult[0]!
    logInfo "here2"
    let b : Q(ZMod $o) ← reconstructTerm pf.getResult[1]!
    logInfo "here3"
    let tac := if ← useNative then ZMod.nativePolyNorm o else ZMod.polyNorm o
    logInfo "here4"
    addTac q($a = $b) tac
--  | .ARITH_POLY_NORM_REL =>
--    if !pf.getChildren[0]!.getResult[0]![0]!.getSort.isInteger then return none
--    reconstructArithPolyNormRel pf
  | _ => return none

end Smt.Reconstruct.ZMod
--set_option pp.all true
-- example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
--   smt

-- example (x: MvPolynomial Nat (ZMod 5)) : (3 :MvPolynomial Nat (ZMod 5)) = 3 := by
--  smt
set_option trace.smt.reconstruct.proof true in
example (x: ZMod 3) : x + x = 2 * x := by
  smt

-- example (x: ZMod 3): x + x + x = 0 := by
--  smt
--
example (x m isz: ZMod 17): (m*x + 16 + isz = 0 ∧ isz * x = 0) →
      ((isz = 0 ∨ isz = 1) ∧ (isz = 1 ↔ x = 0)) := by
      smt

--example (x: ZMod 17): -(-x) = x := by
--  smt
--
--example (x: ZMod 17): x * x ≠ x ∨ x = 1 ∨ x = 0 := by
--  smt

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
