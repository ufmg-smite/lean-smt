/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Data.Rat

import Lean
import Qq

theorem Rat.neg_mul_eq_neg_mul (a b : Rat) : -(a * b) = -a * b := by
  sorry

@[simp] theorem Rat.zero_add (a : Rat) : 0 + a = a := by
  simp [add_def, normalize_eq_mkRat, Int.add_comm, Nat.add_comm, mkRat_self]

namespace Smt.Reconstruct.Rat.PolyNorm

structure Var where
  type : Bool
  val  : Nat
deriving DecidableEq, Repr

instance : LE Var where
  le v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val)

instance : LT Var where
  lt v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val)

instance (v₁ v₂ : Var) : Decidable (v₁ ≤ v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val) then isTrue h else isFalse h

instance (v₁ v₂ : Var) : Decidable (v₁ < v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val) then isTrue h else isFalse h

def Context := Var → Rat

def IntContext := Nat → Int
def RatContext := Nat → Rat

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

open Qq in
def toExpr (m : Monomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Rat) : Q(Rat) :=
  let num : Q(Rat) := mkRatLit c.num.natAbs
  if c.den == 1 then
    if c.num ≥ 0 then
      q($num)
    else
      q(-$num)
  else
    let den : Q(Rat) := mkRatLit c.den
    if c.num ≥ 0 then
      q($num / $den)
    else
      q(-$num / $den)
  mkRatLit (n : Nat) : Q(Rat) :=
    let l : Q(Nat) := Lean.mkRawNatLit n
    q(OfNat.ofNat $l)

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def divConst (m : Monomial) (c : Rat) : Monomial :=
  { m with coeff := m.coeff / c }

def denote (ctx : Context) (m : Monomial) : Rat :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Rat.neg_mul_eq_neg_mul]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx :=
  sorry

theorem denote_divConst {m : Monomial} : (m.divConst c).denote ctx = m.denote ctx / c :=
  sorry

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

open Qq in
def toExpr (p : Polynomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  go p
where
  go : Polynomial → Q(Rat)
    | [] => q(0)
    | [m] => m.toExpr ppCtx
    | m :: ms =>q($(m.toExpr ppCtx) + $(go ms))

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def divConst (p : Polynomial) (c : Rat) : Polynomial :=
  p.map (·.divConst c)

def denote (ctx : Context) (p : Polynomial) : Rat :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx :=
  sorry

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx :=
  sorry

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, Rat.sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx :=
  sorry

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx :=
  sorry

theorem denote_divConst {p : Polynomial} : (p.divConst c).denote ctx = p.denote ctx / c := by
  sorry

end Polynomial

inductive IntExpr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
deriving Inhabited, Repr

namespace IntExpr

def toPolynomial : IntExpr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | neg a => a.toPolynomial.neg
  | add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : IntContext) : IntExpr → Int
  | val v => v
  | var v => ctx v
  | neg a => -a.denote ctx
  | add a b => a.denote ctx + b.denote ctx
  | sub a b => a.denote ctx - b.denote ctx
  | mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {rctx : RatContext} {e : IntExpr} : e.denote ictx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, Rat.intCast_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, Rat.intCast_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, Rat.intCast_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, Rat.intCast_mul, ih₁, ih₂]

end IntExpr

inductive RatExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RatExpr)
  | add (a b : RatExpr)
  | sub (a b : RatExpr)
  | mul (a b : RatExpr)
  | divConst (a : RatExpr) (c : Rat)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RatExpr

def toPolynomial : RatExpr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | neg a => a.toPolynomial.neg
  | add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | mul a b => Polynomial.mul a.toPolynomial b.toPolynomial
  | divConst a c => Polynomial.divConst a.toPolynomial c
  | cast a => a.toPolynomial

def denote (ictx : IntContext) (rctx : RatContext)  : RatExpr → Rat
  | val v => v
  | var v => rctx v
  | neg a => -a.denote ictx rctx
  | add a b => a.denote ictx rctx + b.denote ictx rctx
  | sub a b => a.denote ictx rctx - b.denote ictx rctx
  | mul a b => a.denote ictx rctx * b.denote ictx rctx
  | divConst a c => a.denote ictx rctx / c
  | cast a => a.denote ictx

theorem denote_toPolynomial {e : RatExpr} : e.denote ictx rctx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, ih₁, ih₂]
  | divConst a c ih =>
    simp only [denote, toPolynomial, Polynomial.denote_divConst, ih]
  | cast a =>
    simpa only [denote] using IntExpr.denote_toPolynomial

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : RatExpr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ictx rctx = e₂.denote ictx rctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end PolyNorm.RatExpr

open Lean hiding Rat
open Qq

abbrev PolyM := StateT (Array Q(Int) × Array Q(Rat)) MetaM

def getRatIndex (e : Q(Rat)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := rs.findIdx? (· == e) then
    return i
  else
    let size := rs.size
    set (is, rs.push e)
    return size

def getIntIndex (e : Q(Rat)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e, rs)
    return size

partial def toRatConst (e : Q(Rat)) : PolyM Rat := do
  match e with
  | ~q(OfNat.ofNat $n) => pure n.rawNatLit?.get!
  | ~q(-$x) => pure (-(← toRatConst x))
  | ~q($x + $y) => pure ((← toRatConst x) + (← toRatConst y))
  | ~q($x - $y) => pure ((← toRatConst x) - (← toRatConst y))
  | ~q($x * $y) => pure ((← toRatConst x) * (← toRatConst y))
  | ~q($x / $y) => pure ((← toRatConst x) / (← toRatConst y))
  | e => throwError "[poly_norm] expected a rational number, got {e}"

partial def toQPolyNormIntExpr (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  match e with
  | ~q(OfNat.ofNat $n) => pure q(.val (@OfNat.ofNat Int $n _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormIntExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormIntExpr x) $(← toQPolyNormIntExpr y))
  | e => let v : Nat ← getIntIndex e; pure q(.var $v)

partial def toQPolyNormRatExpr (e : Q(Rat)) : PolyM Q(PolyNorm.RatExpr) := do
  match e with
  | ~q(OfNat.ofNat $n) => pure q(.val (@OfNat.ofNat Rat $n _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormRatExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormRatExpr x) $(← toQPolyNormRatExpr y))
  | ~q($x / $y) => pure q(.divConst $(← toQPolyNormRatExpr x) $(PolyNorm.Monomial.toExpr.toExprCoeff (← toRatConst y)))
  | ~q(($x : Int)) => pure q(.cast $(← toQPolyNormIntExpr x))
  | e => let v : Nat ← getRatIndex e; pure q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRatExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRatExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Rat) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RatContext) := q((«$rs».getD · 0))
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.RatExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (toQPolyNormRatExpr l).run (#[], #[])
  let (r, (is, rs)) ← (toQPolyNormRatExpr r).run (is, rs)
  let is : Q(Array Int) ← pure (is.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let rs : Q(Array Rat) ← pure (rs.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ictx : Q(PolyNorm.IntContext) := q((«$is».getD · 0))
  let rctx : Q(PolyNorm.RatContext) := q((«$rs».getD · 0))
  let h ← nativeDecide q(«$l».toPolynomial = «$r».toPolynomial)
  mv.assign q(@PolyNorm.RatExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxName baseName 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Rat.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Rat.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Rat.Tactic

open Smt.Reconstruct.Rat.PolyNorm.RatExpr

example (x y z : Rat) : 1 * (x + y) * z / 4  = 1/(2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * (x + y) * z / 4  = 1/(2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * (x + y) * z / 4  = 1/(2 * 2) * (z * y + x * z) := by
  native_poly_norm
