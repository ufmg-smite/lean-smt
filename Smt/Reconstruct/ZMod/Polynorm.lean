/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Lean
import Qq
import Mathlib.Data.ZMod.Basic

import Smt.Recognizers

-- private theorem Int.neg_congr {x y : } (h : x = y) : -x = -y := by
--   simp [h]

-- private theorem Int.add_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ + y₁ = x₂ + y₂ := by
--   simp [h₁, h₂]

-- private theorem Int.sub_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ - y₁ = x₂ - y₂ := by
--   simp [h₁, h₂]

-- private theorem Int.mul_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ * y₁ = x₂ * y₂ := by
--   simp [h₁, h₂]

-- private theorem Eq.trans₂' (hba : b = a) (hbc : b = c) (hcd : c = d) : a = d := hba ▸ hbc ▸ hcd ▸ rfl

namespace Smt.Reconstruct.ZMod.PolyNorm

abbrev Var := Nat

def Context (n : Nat) := Var → ZMod n


structure Monomial (n : Nat) where
  coeff : ZMod n
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

open Qq in
def toExpr {n : Nat} (m : Monomial n) (ppCtx : Var → Q(ZMod $n)) : Q(ZMod $n) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : ZMod n) : Q(ZMod $n) :=
    let l : Q(Nat) := Lean.mkRawNatLit c.val
    q(OfNat.ofNat $l : ZMod $n)


def neg (m : Monomial n) : Monomial n :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial n) (_ : m₁.vars = m₂.vars) : Monomial n :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial n) : Monomial n :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def denote (ctx : Context n) (m : Monomial n) : ZMod n :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial n} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, neg_mul_eq_neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end

-- Can be generalized.
theorem foldl_mul_insert {ctx : Context n} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    --simp [mul.insert, h, foldl_assoc,]
    · simp [mul.insert, h, foldl_assoc mul_assoc (ctx y) (ctx x)]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, mul_comm,
                 foldl_assoc mul_assoc, ih]
      rw [←mul_assoc, mul_comm (ctx x) (ctx y), mul_assoc]

theorem denote_add {ctx: Context o} {m n : Monomial o} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, add_mul, h]

theorem denote_mul{ctx: Context o}  {m₁ m₂ : Monomial o} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, mul_assoc]; congr 1
  rw [← mul_assoc, mul_comm _ m₂.coeff, mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc mul_assoc, ih]

end Monomial

abbrev Polynomial n := List (Monomial n)

namespace Polynomial


-- open Qq in
-- def toExpr {n : Nat} (m : Monomial n) (ppCtx : Var → Q(ZMod $n)) : Q(ZMod $n) :=
--   if h : m.vars = [] then
--     toExprCoeff m.coeff
--   else
--     if m.coeff = 1 then
--       (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
--     else
--       m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
-- where
--   toExprCoeff (c : ZMod n) : Q(ZMod $n) :=
--     let l : Q(Nat) := Lean.mkRawNatLit c.val
--     q(OfNat.ofNat $l : ZMod $n)

open Qq in
def toExpr {n : Nat} (p : Polynomial n) (ppCtx : Var → Q(ZMod $n)) : Q(ZMod $n) :=
  go p
where
  go : Polynomial n → Q(ZMod $n)
    | [] => q(0)
    | [m] => m.toExpr ppCtx
    | m :: ms =>q($(m.toExpr ppCtx) + $(go ms))

def neg (p : Polynomial n) : Polynomial n :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial n) : Polynomial n :=
  p.foldr insert q
where
  insert (m : Monomial n) : Polynomial n → Polynomial n
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial n) : Polynomial n :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial n) (p : Polynomial n) : Polynomial n :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial n) : Polynomial n :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def denote (ctx : Context n) (p : Polynomial n) : ZMod n :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

-- ⊢ List.foldl (fun z a => z + Monomial.denote ctx a) 0
--     (if h : m.vars = n.vars then if (m.add n ⋯).coeff = 0 then p else m.add n ⋯ :: p else n :: add.insert m p) =
--   Monomial.denote ctx m + (Monomial.denote ctx n + List.foldl (fun z a => z + Monomial.denote ctx a) 0 p)

theorem foldl_add_insert (ctx : Context o) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, add_comm (0 : ZMod o), Monomial.foldl_assoc add_assoc ]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←add_assoc, add_comm, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq]
        · simp [-add_zero, add_comm (0:ZMod o), Monomial.foldl_assoc add_assoc, Monomial.denote_add, add_assoc]
      · simp only [List.foldl_cons, add_comm (0: ZMod o), ih, Monomial.foldl_assoc add_assoc]
        rw [←add_assoc, add_comm (Monomial.denote ctx n), add_assoc]

theorem denote_neg {p : Polynomial o} : p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, add_comm (0:ZMod o), Monomial.foldl_assoc add_assoc,neg_add, ←ih, List.map, Monomial.denote_neg]

theorem denote_add {p q : Polynomial n} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, add_comm (0:ZMod n), Monomial.foldl_assoc add_assoc, add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial n} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial o} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, add_comm (0 :ZMod o), Monomial.foldl_assoc add_assoc, mul_add, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

theorem denote_cons {p : List (Monomial n)} {ctx : Context n} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  simp only [denote, List.foldl_cons, add_comm (0 :ZMod n), Monomial.foldl_assoc add_assoc]

theorem denote_nil_add : denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, denote_cons, show denote ctx [] = 0 by rfl]

theorem denote_add_insert {g : Monomial o → Polynomial o} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih, @ih ((g k).add []), ← add_assoc, denote_nil_add, denote_add, add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial o → Polynomial o} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) (0 :ZMod o) p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, add_comm] at *
    rw [add_comm (0:ZMod o), Monomial.foldl_assoc add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial n} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx := by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, add_mul, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

end Polynomial

inductive Expr (o : Nat) where
  | val (v : ZMod o)
  | var (v : Nat)
  | neg (a : Expr o)
  | add (a b : Expr o)
  | sub (a b : Expr o)
  | mul (a b : Expr o)
deriving Inhabited, Repr

namespace Expr

-- o is the modulus (a Nat), not a ZMod o element.
def toPolynomial {o : Nat} : Expr o → Polynomial o
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := (1 : ZMod o), vars := [v] }]
  | .neg a => Polynomial.neg (toPolynomial a)
  | .add a b => Polynomial.add (toPolynomial a) (toPolynomial b)
  | .sub a b => Polynomial.sub (toPolynomial a) (toPolynomial b)
  | .mul a b => Polynomial.mul (toPolynomial a) (toPolynomial b)

def denote (ctx : Context o) : Expr o → ZMod o
  | val v => v
  | var v => ctx v
  | neg a => -a.denote ctx
  | add a b => a.denote ctx + b.denote ctx
  | sub a b => a.denote ctx - b.denote ctx
  | mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {e : Expr o} : denote (o:=o) ctx e  = (toPolynomial (o:=o) e).denote ctx := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv];  rfl
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

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr o} (h : e₁.toPolynomial (o := o)  = e₂.toPolynomial (o := o)  ) : e₁.denote (o:=o) ctx = e₂.denote (o:=o) ctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]


end PolyNorm.Expr

open Lean Qq

abbrev PolyM (n : Nat) := StateT (Array (Q(ZMod $n))) MetaM

def getIndex (n : Nat) (e : Q(ZMod $n)) : PolyM n Nat := do
  let is ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e)
    return size

partial def reify (n : Nat) (e : Q(ZMod $n)) : PolyM n (Q(PolyNorm.Expr $n)) := do
  if let some k := e.natLitOf? q(ZMod $n) then
    return q(.val (OfNat.ofNat $k))
  else if let some e' := e.negOf? q(ZMod $n) then
    return q(.neg $(← reify n e'))
  else if let some (x, y) := e.hAddOf? q(ZMod $n) q(ZMod $n) then
    return q(.add $(← reify n x) $(← reify n y))
  else if let some (x, y) := e.hSubOf? q(ZMod $n) q(ZMod $n) then
    return q(.sub $(← reify n x) $(← reify n y))
  else if let some (x, y) := e.hMulOf? q(ZMod $n) q(ZMod $n) then
    return q(.mul $(← reify n x) $(← reify n y))
  else
    let v : Nat ← getIndex n e
    return q(.var $v)

def polyNorm (n:Nat) (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(ZMod $n)), (r : Q(ZMod $n))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, is) ← (reify n l).run #[]
  let (r, is) ← (reify n r).run is

  let ctx : Q(PolyNorm.Context $n) ← if h : 0 < is.size
    then do let is : Q(RArray (ZMod $n)) ← (RArray.ofArray is h).toExpr q(ZMod $n) id; pure q(«$is».get)
    else pure q(fun _ => (0))

  let hp : Q(«$l».toPolynomial (o := $n) = «$r».toPolynomial (o := $n)) :=
    (.app q(@Eq.refl (PolyNorm.Polynomial $n)) q(«$l».toPolynomial (o := $n)))

  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq (o := $n) $ctx  $l $r $hp)
  mv.assign he
where
  logPolynomial (n : Nat)  (e : Q(PolyNorm.Expr $n)) (es : Array Q(ZMod $n)) := do
    let p ← unsafe Meta.evalExpr (PolyNorm.Expr n) q(PolyNorm.Expr $n) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"


def nativePolyNorm (n:Nat) (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(ZMod $n)), (r : Q(ZMod $n))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, is) ← (reify n l).run #[]
  let (r, is) ← (reify n r).run is
  let ctx : Q(PolyNorm.Context $n) ← if h : 0 < is.size
    then do let is : Q(RArray (ZMod $n)) ← (RArray.ofArray is h).toExpr q(ZMod $n) id; pure q(«$is».get)
    else pure q(fun _ => (0))
  let hp ← nativeDecide q(«$l».toPolynomial = «$r».toPolynomial)
  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq (o := $n) $ctx $l $r $hp)
  mv.assign he
where
  logPolynomial (n:Nat) (e : Q(PolyNorm.Expr $n)) (es : Array Q(ZMod $n)) := do
    let p ← unsafe Meta.evalExpr (PolyNorm.Expr n) q(PolyNorm.Expr) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxDeclName baseName
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
    let mv ← getMainGoal
    let goalTy ← mv.getType
    let some (_, l, r) := goalTy.eq?
      | throwError "[poly_norm] expected an equality, got {goalTy}"
    let lTy ← Lean.Meta.inferType l
    let (fn, args) := lTy.getAppFnArgs
    logInfo m!"{fn}, {args}"
    let nExpr ←
      match fn, args with
      |  ``ZMod, #[n] => pure n
      | _, _ => throwError "[poly_norm] expected lhs type ZMod n, got {lTy}"
    let nExpr ← Lean.Meta.whnf nExpr
    let nVal ←
      match nExpr with
      | Expr.lit (Lean.Literal.natVal k) => pure k
      | _ => throwError "[poly_norm] modulus is not a numeral; got {nExpr}"
    ZMod.polyNorm nVal mv
    replaceMainGoal []
syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← getMainGoal
    let goalTy ← mv.getType
    let some (_, l, r) := goalTy.eq?
      | throwError "[poly_norm] expected an equality, got {goalTy}"
    let lTy ← Lean.Meta.inferType l
    let (fn, args) := lTy.getAppFnArgs
    logInfo m!"{fn}, {args}"
    let nExpr ←
      match fn, args with
      |  ``ZMod, #[n] => pure n
      | _, _ => throwError "[poly_norm] expected lhs type ZMod n, got {lTy}"
    let nExpr ← Lean.Meta.whnf nExpr
    let nVal ←
      match nExpr with
      | Expr.lit (Lean.Literal.natVal k) => pure k
      | _ => throwError "[poly_norm] modulus is not a numeral; got {nExpr}"
    ZMod.nativePolyNorm nVal mv
    replaceMainGoal []

end Smt.Reconstruct.ZMod.Tactic

example (x y z : ZMod 3) : 1 * (x + y) * z  = z * y + x * z := by
  poly_norm

example (x y z : ZMod 3) : 1 * (x + y) * z  = z * y + x * z := by
  native_poly_norm
