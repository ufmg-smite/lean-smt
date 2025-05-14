/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Smt.Recognizers

namespace Smt.Reconstruct.Real.PolyNorm

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

def Context := Var → Real

def IntContext := Nat → Int
def RealContext := Nat → Real

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

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

def denote (ctx : Context) (m : Monomial) : Real :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, neg_mul_eq_neg_mul, Rat.cast_neg]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end
-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc mul_assoc (ctx y) (ctx x), mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, mul_comm,
                 foldl_assoc mul_assoc, ih]
      rw [←mul_assoc, mul_comm (ctx x) (ctx y), mul_assoc]

theorem denote_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, add_mul, h, Rat.cast_add]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, mul_assoc, Rat.cast_mul]; congr 1
  rw [←mul_assoc, mul_comm _ (m₂.coeff : Real), mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Rat.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc mul_assoc, ih]

theorem denote_divConst {m : Monomial} : (m.divConst c).denote ctx = m.denote ctx / c := by
  simp only [denote, divConst, mul_div_right_comm, Rat.cast_div]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

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

def denote (ctx : Context) (p : Polynomial) : Real :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc, zero_add]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←add_zero (Monomial.denote ctx n), Monomial.foldl_assoc add_assoc, ←add_assoc, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq, add_zero]
        · simp [add_comm 0, Monomial.foldl_assoc add_assoc, Monomial.denote_add, heq, add_assoc]
      · rw [←zero_add (Monomial.denote ctx n), List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc, Monomial.foldl_assoc add_assoc, ih]
        rw [←add_assoc, add_comm (Monomial.denote ctx n), add_assoc]

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc, neg_add, ←ih, List.map]
    rw [List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc, Monomial.denote_neg]

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    rw [List.foldr_cons, List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc, add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    rw [List.foldl_cons, List.foldr_cons, add_comm 0, Monomial.foldl_assoc add_assoc, mul_add, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

theorem denote_cons {p : List Monomial} {ctx : Context} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  rw [denote, List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc]
  simp [denote, Monomial.foldl_assoc add_assoc]

theorem denote_nil_add : denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, List.foldr_cons, denote_cons, ih, show denote ctx [] = 0 by rfl, add_zero]

theorem denote_add_insert {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote, add_zero]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← add_assoc, denote_nil_add, denote_add, add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) 0 p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, add_comm, List.foldr] at *
    rw [add_comm 0, Monomial.foldl_assoc add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx :=by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, add_mul, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

theorem denote_divConst {p : Polynomial} : (p.divConst c).denote ctx = p.denote ctx / c := by
  simp only [denote, divConst]
  induction p with
  | nil => simp [zero_div]
  | cons x ys ih =>
    rw [List.map_cons, List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc]
    rw [List.foldl_cons, add_comm 0, Monomial.foldl_assoc add_assoc]
    rw [Monomial.denote_divConst, ih, add_div]

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
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : IntContext) : IntExpr → Int
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.denote ctx
  | .add a b => a.denote ctx + b.denote ctx
  | .sub a b => a.denote ctx - b.denote ctx
  | .mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {rctx : RealContext} {e : IntExpr} : e.denote ictx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv, Int.cast_zero]; rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, Int.cast_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, Int.cast_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, Int.cast_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, Int.cast_mul, ih₁, ih₂]

end IntExpr

inductive RealValExpr where
  | val (v : Rat)
  | neg (a : RealValExpr)
  | add (a b : RealValExpr)
  | sub (a b : RealValExpr)
  | mul (a b : RealValExpr)
  | div (a : RealValExpr) (c : RealValExpr)
deriving Inhabited, Repr

namespace RealValExpr

def eval : RealValExpr → Rat
  | .val v => v
  | .neg a => -a.eval
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .div a c => a.eval / c.eval

noncomputable def denote : RealValExpr → Real
  | .val v => if v = 0 then 0 else if v = 1 then 1 else v
  | .neg a => -a.denote
  | .add a b => a.denote + b.denote
  | .sub a b => a.denote - b.denote
  | .mul a b => a.denote * b.denote
  | .div a c => a.denote / c.denote

theorem eval_eq_denote {e : RealValExpr} : e.eval = e.denote := by
  induction e with
  | val v =>
    simp only [eval, denote]
    split <;> rename_i hv
    · simp only [Rat.cast_zero, hv]
    · split <;> rename_i hv
      · simp only [Rat.cast_one, hv]
      · simp only [hv]
  | neg a ih =>
    simp only [eval, denote, Rat.cast_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, denote, Rat.cast_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, denote, Rat.cast_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, denote, Rat.cast_mul, ih₁, ih₂]
  | div a c ih₁ ih₂ =>
    simp only [eval, denote, Rat.cast_div, ih₁, ih₂]

end RealValExpr

inductive RealExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RealExpr)
  | add (a b : RealExpr)
  | sub (a b : RealExpr)
  | mul (a b : RealExpr)
  | divConst (a : RealExpr) (c : RealValExpr)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RealExpr

def toPolynomial : RealExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial
  | .divConst a c => Polynomial.divConst a.toPolynomial c.eval
  | .cast a => a.toPolynomial

noncomputable def denote (ictx : IntContext) (rctx : RealContext) : RealExpr → Real
  | .val v => if v = 0 then 0 else if v = 1 then 1 else v
  | .var v => rctx v
  | .neg a => -a.denote ictx rctx
  | .add a b => a.denote ictx rctx + b.denote ictx rctx
  | .sub a b => a.denote ictx rctx - b.denote ictx rctx
  | .mul a b => a.denote ictx rctx * b.denote ictx rctx
  | .divConst a c => a.denote ictx rctx / c.denote
  | .cast a => a.denote ictx

theorem denote_toPolynomial {e : RealExpr} : e.denote ictx rctx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial, Polynomial.denote, Monomial.denote]
    split <;> rename_i hv
    · simp [Rat.cast_zero, hv]
    · split <;> rename_i hv
      · simp [Rat.cast_one, hv]
      · simp [hv]
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
    simp only [denote, toPolynomial, Polynomial.denote_divConst, RealValExpr.eval_eq_denote, ih]
  | cast a =>
    simpa only [denote] using IntExpr.denote_toPolynomial

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : RealExpr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ictx rctx = e₂.denote ictx rctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end PolyNorm.RealExpr

open Lean Qq

abbrev PolyM := StateT (Array Q(Int) × Array Q(Real)) MetaM

def getIntIndex (e : Q(Int)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e, rs)
    return size

def getRealIndex (e : Q(Real)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := rs.findIdx? (· == e) then
    return i
  else
    let size := rs.size
    set (is, rs.push e)
    return size

partial def reifyRealVal (e : Q(Real)) : PolyM Q(PolyNorm.RealValExpr) := do
  if let some n := e.natLitOf? q(Real) then
    return q(.val (OfNat.ofNat $n))
  else if let some e := e.negOf? q(Real) then
    return q(.neg $(← reifyRealVal e))
  else if let some (x, y) := e.hAddOf? q(Real) q(Real) then
    return q(.add $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hSubOf? q(Real) q(Real) then
    return q(.sub $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hMulOf? q(Real) q(Real) then
    return q(.mul $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hDivOf? q(Real) q(Real) then
    return q(.div $(← reifyRealVal x) $(← reifyRealVal y))
  else
    throwError "[poly_norm] expected a rational number, got {e}"

partial def reifyInt (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  if let some e := e.natLitOf? q(Int) then
    return q(.val (OfNat.ofNat $e))
  else if let some e := e.negOf? q(Int) then
    return q(.neg $(← reifyInt e))
  else if let some (x, y) := e.hAddOf? q(Int) q(Int) then
    return q(.add $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hSubOf? q(Int) q(Int) then
    return q(.sub $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hMulOf? q(Int) q(Int) then
    return q(.mul $(← reifyInt x) $(← reifyInt y))
  else
    let v : Nat ← getIntIndex e
    return q(.var $v)

partial def reifyReal (e : Q(Real)) : PolyM Q(PolyNorm.RealExpr) := do
  if let some e := e.natLitOf? q(Real) then
    return q(.val (OfNat.ofNat $e))
  else if let some e := e.negOf? q(Real) then
    return q(.neg $(← reifyReal e))
  else if let some (x, y) := e.hAddOf? q(Real) q(Real) then
    return q(.add $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hSubOf? q(Real) q(Real) then
    return q(.sub $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hMulOf? q(Real) q(Real) then
    return q(.mul $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hDivOf? q(Real) q(Real) then
    return q(.divConst $(← reifyReal x) $(← reifyRealVal y))
  else if let some e := e.intCastOf? q(Real) then
    return q(.cast $(← reifyInt e))
  else
    let v : Nat ← getRealIndex e
    return q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyReal l).run (#[], #[])
  let (r, (is, rs)) ← (reifyReal r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) := if h : 0 < is.size
    then let is : Q(RArray Int) := (RArray.ofArray is h).toExpr q(Int) id; q(«$is».get)
    else q(fun _ => 0)
  let rctx : Q(PolyNorm.RealContext) := if h : 0 < rs.size
    then let rs : Q(RArray Real) := (RArray.ofArray rs h).toExpr q(Real) id; q(«$rs».get)
    else q(fun _ => 0)
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.RealExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyReal l).run (#[], #[])
  let (r, (is, rs)) ← (reifyReal r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) := if h : 0 < is.size
    then let is : Q(RArray Int) := (RArray.ofArray is h).toExpr q(Int) id; q(«$is».get)
    else q(fun _ => 0)
  let rctx : Q(PolyNorm.RealContext) := if h : 0 < rs.size
    then let rs : Q(RArray Real) := (RArray.ofArray rs h).toExpr q(Real) id; q(«$rs».get)
    else q(fun _ => 0)
  let h ← nativeDecide q(«$l».toPolynomial = «$r».toPolynomial)
  mv.assign q(@PolyNorm.RealExpr.denote_eq_from_toPolynomial_eq $ictx $rctx $l $r $h)
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← match (← getEnv).asyncPrefix? with
      | none          => Lean.mkAuxName baseName 1
      | some declName => Lean.mkAuxName (declName ++ baseName) 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  if let some (_, mv) ← normNumAt mv (← Meta.Simp.mkContext) #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Real.Tactic

example (x y z : Real) : 1 * (x + y) * z / 4 = 1 / (2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * (↑x + ↑y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  native_poly_norm
