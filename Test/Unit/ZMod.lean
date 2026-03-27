import Smt
import Smt.ZMod
import Smt.Reconstruct.ZMod.Polynorm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nullstellensatz

namespace Smt.Translate.ZMod

open Lean Expr
open Qq
open Translator Term
open Smt
open Reconstruct

private def reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
  let some n ← (Meta.evalNat (← Meta.whnf n)).run | throwError "literal{indentD n}\nis not constant in{indentD e}"
  return n

private def reduceZModOrder? (e : Expr) : MetaM (Option Nat) := do
  let some o := e.app1? ``ZMod | return none
  let some o' ← (Meta.evalNat o).run | throwError "zmod type{indentD e}\nhas variable order"
  if (← Meta.synthInstance? q(Fact «$o'».Prime)).isNone then
    throwError "zmod order{indentD o}\nis not known to be a prime in{indentD e}\nMissing [{q(Fact «$o'».Prime)}] instance?"
  return o'

@[smt_translate] def translateType : Translator := fun e => do
  if let some o ← reduceZModOrder? e then
    return mkApp2 (symbolT "_") (symbolT "FiniteField") (literalT (toString o))
  else
    return none

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
  | _ => return none

end Smt.Translate.ZMod

/-- Expressions over variables `σ` with coefficients in `ZMod n`. -/
inductive ZModExpr (n : Nat) where
| var   : Nat → ZModExpr n
| const : ZMod n → ZModExpr n
| add   : ZModExpr n  → ZModExpr n  → ZModExpr n
| mul   : ZModExpr n  → ZModExpr n  → ZModExpr n
| neg   : ZModExpr n  → ZModExpr n

prefix:75 "-ₚ"   => ZModExpr.neg
infixl:65 " +ₚ " => ZModExpr.add
infixl:70 " *ₚ " => ZModExpr.mul

@[app_unexpander ZModExpr.const]
def unexpandZModExprConst : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => ``($x)
  | _ => throw ()

namespace ZModExpr

def toZMod (ctx: Nat → ZMod n) (p: ZModExpr n) : ZMod n :=
  match p with
  | .var i     => ctx i
  | .const c   => c
  | .add a b   => toZMod ctx a + toZMod ctx b
  | .mul a b   => toZMod ctx a * toZMod ctx b
  | .neg a     =>  -(toZMod ctx a)

noncomputable def toPoly : ZModExpr n → MvPolynomial Nat (ZMod n)
  | var i => .X i
  | const c => .C c
  | add a b => toPoly a + toPoly b
  | mul a b => toPoly a * toPoly b
  | neg a => -toPoly a

open Qq Lean

abbrev ZModExprM (n : Nat) := StateT (Array Q(ZMod $n)) MetaM

def getIndex (n : Nat) (e : Q(ZMod $n)) : ZModExprM n Nat := do
  let is ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e)
    return size

partial def reify (n : Nat) (e : Q(ZMod $n)) : ZModExprM n (Q(ZModExpr $n)) := do
  if let some _ := e.natLitOf? q(ZMod $n) then
    return q(.const $e)
  else if let some e' := e.negOf? q(ZMod $n) then
    return q(.neg $(← reify n e'))
  else if let some (x, y) := e.hAddOf? q(ZMod $n) q(ZMod $n) then
    return q(.add $(← reify n x) $(← reify n y))
  else if let some (x, y) := e.hMulOf? q(ZMod $n) q(ZMod $n) then
    return q(.mul $(← reify n x) $(← reify n y))
  else
    let v : Nat ← getIndex n e
    return q(.var $v)

end ZModExpr

namespace Smt.Reconstruct.ZMod

open Lean Qq

abbrev MvPolynomialM (n : Nat) := StateT (Array Q(ZMod $n)) MetaM

namespace MvPolynomialM

def getIndex (n : Nat) (e : Q(ZMod $n)) : MvPolynomialM n Nat := do
  let is ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e)
    return size

partial def reify (n : Nat) (e : Q(ZMod $n)) : MvPolynomialM n (Q(MvPolynomial Nat (ZMod $n))) := do
  if let some _ := e.natLitOf? q(ZMod $n) then
    return q(.C $e)
  else if let some e' := e.negOf? q(ZMod $n) then
    return q(-$(← reify n e'))
  else if let some (x, y) := e.hAddOf? q(ZMod $n) q(ZMod $n) then
    return q($(← reify n x) + $(← reify n y))
  else if let some (x, y) := e.hMulOf? q(ZMod $n) q(ZMod $n) then
    return q($(← reify n x) * $(← reify n y))
  else
    let v : Nat ← getIndex n e
    return q(.X $v)

end MvPolynomialM

def ideal (ps : List (MvPolynomial Nat (ZMod n))) : Ideal (MvPolynomial Nat (ZMod n)) :=
  Ideal.span ps.toFinset

def variety [Fact n.Prime] (I : Ideal (MvPolynomial Nat (ZMod n))) : Set (Nat → ZMod n) :=
  MvPolynomial.zeroLocus (ZMod n) I

theorem eq_of_add_neg_eq [Fact n.Prime] {c₁ c₂ : ZMod n} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ + -a₂) = c₂ * (b₁ + -b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    rewrite [ha, add_neg_cancel, mul_zero, eq_comm, mul_eq_zero] at h
    have h := h.resolve_left hc₂
    exact eq_of_add_neg_eq_zero h
  · intro hb
    rewrite [hb, add_neg_cancel, mul_zero, mul_eq_zero] at h
    have h := h.resolve_left hc₁
    exact eq_of_add_neg_eq_zero h

theorem ideal_generator : y ∈ ideal (xs ++ y :: zs) := by
  exact Ideal.subset_span (by simp)

theorem one_unsat [Fact n.Prime] {ps : List (MvPolynomial Nat (ZMod n))} (h : 1 ∈ ideal ps)
  : variety (ideal ps) = ∅ := by
  have htop : ideal ps = ⊤ := Ideal.eq_top_of_isUnit_mem _ h isUnit_one
  simp [variety, htop]

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
  | .FINITE_FIELD_IDEAL =>
    let o :  Nat := t[0]!.getSort.getFiniteFieldSize!
    let mut ps : Q(List (MvPolynomial Nat (ZMod $o))) := q([])
    -- TODO: we lose the `is`, which is the reification context for `MvPolynomialM`. We should
    -- maintain it to avoid mismatches between mutliple reifications of the same term.
    let mut is : Array Q(ZMod $o) := #[]
    for i in t.getChildren.reverse do
      let p : Q(ZMod $o) ← reconstructTerm i
      let (p, is') ← (MvPolynomialM.reify o p).run is
      is := is'
      ps := q($p :: $ps)
    return q(ideal $ps)
  | .FINITE_FIELD_VARIETY =>
    let o:  Nat := t.getSort.getSetElementSort!.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let s : Q(Ideal (MvPolynomial Nat (ZMod $o))) ← reconstructTerm t[0]!
    return q(@variety $o $ho $s)
  | .SET_MEMBER =>
    if t[1]!.getKind != .FINITE_FIELD_IDEAL then return none
    let o : Nat := t[0]!.getSort.getFiniteFieldSize!
    let x : Q(ZMod $o) ← reconstructTerm t[0]!
    -- TODO: we lose the `is`, which is the reification context for `MvPolynomialM`. We should
    -- maintain it to avoid mismatches between mutliple reifications of the same term.
    let (x, _) ← (MvPolynomialM.reify o x).run #[]
    let s : Q(Ideal (MvPolynomial Nat (ZMod $o))) ← reconstructTerm t[1]!
    return q($x ∈ $s)
  | .SET_IS_EMPTY =>
    if t[0]!.getKind != .FINITE_FIELD_VARIETY then return none
    let o : Nat := t[0]!.getSort.getSetElementSort!.getFiniteFieldSize!
    let s : Q(Set (Nat → ZMod $o)) ← reconstructTerm t[0]!
    return q($s = ∅)
  | .SKOLEM => match t.getSkolemId! with
    | .FF_DISEQ =>
      let o : Nat := t.getSort.getFiniteFieldSize!
      let t := t.getSkolemIndices![0]! -- (not (= a b))
      let a : Q(ZMod $o) ← reconstructTerm (t[0]!)[0]!
      let b : Q(ZMod $o) ← reconstructTerm (t[0]!)[1]!
      return q(Classical.epsilon (fun x => x * ($a - $b) - 1 = 0))
    | _ => return none
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
  | _ => return none

open Qq

@[smt_proof_reconstruct] def reconstructFfProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .FF_POLY_NORM =>
    if !pf.getResult[0]!.getSort.isFiniteField then return none
    let o : Nat := pf.getResult[0]!.getSort.getFiniteFieldSize!
    let a : Q(ZMod $o) ← reconstructTerm pf.getResult[0]!
    let b : Q(ZMod $o) ← reconstructTerm pf.getResult[1]!
    let tac := if ← useNative then ZMod.nativePolyNorm o else ZMod.polyNorm o
    addTac q($a = $b) tac
  | .FF_POLY_NORM_EQ =>
    let o : Nat := (pf.getChildren[0]!.getResult[0]!)[0]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let cx : Q(ZMod $o) ← reconstructTerm (pf.getChildren[0]!.getResult[0]!)[0]!
    let cy : Q(ZMod $o) ← reconstructTerm (pf.getChildren[0]!.getResult[1]!)[0]!
    let x₁ : Q(ZMod $o) ← reconstructTerm (pf.getResult[0]!)[0]!
    let x₂ : Q(ZMod $o) ← reconstructTerm (pf.getResult[0]!)[1]!
    let y₁ : Q(ZMod $o) ← reconstructTerm (pf.getResult[1]!)[0]!
    let y₂ : Q(ZMod $o) ← reconstructTerm (pf.getResult[1]!)[1]!
    let hcx : Q($cx ≠ 0) := .app q(@of_decide_eq_true ($cx ≠ 0) _) q(Eq.refl true)
    let hcy : Q($cy ≠ 0) := .app q(@of_decide_eq_true ($cy ≠ 0) _) q(Eq.refl true)
    let h : Q($cx * ($x₁ + -$x₂) = $cy * ($y₁ + -$y₂)) ← reconstructProof pf.getChildren[0]!
    addThm q(($x₁ = $x₂) = ($y₁ = $y₂)) q(@eq_of_add_neg_eq $o $x₁ $x₂ $y₁ $y₂ $ho $cx $cy $hcx $hcy $h)
  | .FF_IDEAL_GENERATOR =>
    let o : Nat := pf.getResult[0]!.getSort.getFiniteFieldSize!
    let y : Q(ZMod $o) ← reconstructTerm pf.getResult[0]!
    let (y, is) ← (MvPolynomialM.reify o y).run #[]
    let ps := pf.getResult[1]!.getChildren
    let [xs, zs] := ps.toList.splitOn pf.getResult[0]!
      | throwError "unexpected number of generators in ideal: {ps.size}, expected at least 1"
    let reconstructMVPs := fun (t : cvc5.Term) ((acc, is) : Q(List (MvPolynomial Nat (ZMod $o))) × Array Q(ZMod «$o»)) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let (p, is) ← (MvPolynomialM.reify o p).run is
      return (q($p :: $acc), is)
    let (xs, is) ← xs.foldrM reconstructMVPs (q([]), is)
    let (zs, _) ← zs.foldrM reconstructMVPs (q([]), is)
    addThm q($y ∈ ideal ($xs ++ $y :: $zs)) q(@ideal_generator $o $xs $y $zs)
  | .FF_ONE_UNSAT =>
    let o : Nat := pf.getChildren[0]!.getResult[0]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let ps := pf.getChildren[0]!.getResult[1]!.getChildren
    let reconstructMVPs := fun (t : cvc5.Term) ((acc, is) : Q(List (MvPolynomial Nat (ZMod $o))) × Array Q(ZMod «$o»)) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let (p, is) ← (MvPolynomialM.reify o p).run is
      return (q($p :: $acc), is)
    let ((ps : Q(List (MvPolynomial Nat (ZMod $o)))), _) ← ps.foldrM reconstructMVPs (q([]), #[])
    let h : Q(1 ∈ ideal $ps) ← reconstructProof pf.getChildren[0]!
    addThm q(variety (ideal $ps) = ∅) q(@one_unsat $o $ho $ps $h)
  | _ => return none

end Smt.Reconstruct.ZMod

open Smt.Reconstruct.ZMod
open MvPolynomial ZModExpr

set_option trace.smt true
set_option trace.smt.reconstruct.proof true
set_option trace.smt.solve true
set_option pp.instantiateMVars false

--set_option pp.all true
example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
  smt

-- example (x: MvPolynomial Nat (ZMod 5)) : (3 :MvPolynomial Nat (ZMod 5)) = 3 := by
--  smt
set_option trace.smt.reconstruct.proof true in
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
 smt +trust +model
 sorry

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
