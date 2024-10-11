/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Lean
import Qq

private theorem Int.neg_congr {x y : Int} (h : x = y) : -x = -y := by
  simp [h]

private theorem Int.add_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ + y₁ = x₂ + y₂ := by
  simp [h₁, h₂]

private theorem Int.sub_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ - y₁ = x₂ - y₂ := by
  simp [h₁, h₂]

private theorem Int.mul_congr {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) : x₁ * y₁ = x₂ * y₂ := by
  simp [h₁, h₂]

private theorem Eq.trans₂' (hba : b = a) (hbc : b = c) (hcd : c = d) : a = d := hba ▸ hbc ▸ hcd ▸ rfl

namespace Smt.Reconstruct.Int.PolyNorm

abbrev Var := Nat

def Context := Var → Int

structure Monomial where
  coeff : Int
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

open Qq in
def toExpr (m : Monomial) (ppCtx : Var → Q(Int)) : Q(Int) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Int) : Q(Int) :=
    let l : Q(Nat) := Lean.mkRawNatLit c.natAbs
    if c ≥ 0 then
      q(OfNat.ofNat $l : Int)
    else
      q(-OfNat.ofNat $l : Int)

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

def denote (ctx : Context) (m : Monomial) : Int :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Int.neg_mul_eq_neg_mul]

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
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [List.foldl]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Int.mul_assoc (ctx y) (ctx x), Int.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Int.mul_comm,
                 foldl_assoc Int.mul_assoc, ih]
      rw [←Int.mul_assoc, Int.mul_comm (ctx x) (ctx y), Int.mul_assoc]

theorem denote_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, Int.add_mul, h]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, Int.mul_assoc]; congr 1
  rw [← Int.mul_assoc, Int.mul_comm _ m₂.coeff, Int.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Int.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Int.mul_assoc, ih]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

open Qq in
def toExpr (p : Polynomial) (ppCtx : Var → Q(Int)) : Q(Int) :=
  go p
where
  go : Polynomial → Q(Int)
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

def denote (ctx : Context) (p : Polynomial) : Int :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Int.add_assoc, Int.add_comm, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq]
        · simp [-Int.add_zero, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.denote_add, heq, Int.add_assoc]
      · simp only [List.foldl_cons, Int.add_comm 0, ih, Monomial.foldl_assoc Int.add_assoc]
        rw [←Int.add_assoc, Int.add_comm (Monomial.denote ctx n), Int.add_assoc]

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc,Int.neg_add, ←ih, List.map, Monomial.denote_neg]

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, Int.sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

theorem denote_cons {p : List Monomial} {ctx : Context} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  simp only [denote, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]

theorem denote_nil_add : denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, List.foldr_cons, denote_cons, ih, show denote ctx [] = 0 by rfl]

theorem denote_add_insert {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Int.add_assoc, denote_nil_add, denote_add, Int.add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) 0 p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, Int.add_comm, List.foldr] at *
    rw [Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx := by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, Int.add_mul, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

end Polynomial

inductive Expr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | mul (a b : Expr)
  | sub (a b : Expr)
deriving Inhabited, Repr

namespace Expr

def toPolynomial : Expr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [v] }]
  | neg a => a.toPolynomial.neg
  | add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : Context) : Expr → Int
  | val v => v
  | var v => ctx v
  | neg a => -a.denote ctx
  | add a b => a.denote ctx + b.denote ctx
  | sub a b => a.denote ctx - b.denote ctx
  | mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {e : Expr} : e.denote ctx = e.toPolynomial.denote ctx := by
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

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ctx = e₂.denote ctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end PolyNorm.Expr

open Lean Qq

partial def genCtx (e : Q(Int)) : StateT (Array Q(Int) × HashSet Q(Int)) MetaM Unit := do
  if !(← get).snd.contains e then
    go
    modify fun (es, cache) => (es, cache.insert e)
where
  go : StateT (Array Q(Int) × HashSet Q(Int)) MetaM Unit := do
  match e with
  | ~q(OfNat.ofNat $x) => pure ()
  | ~q(-$x)            => genCtx x
  | ~q($x + $y)        => genCtx x >>= fun _ => genCtx y
  | ~q($x - $y)        => genCtx x >>= fun _ => genCtx y
  | ~q($x * $y)        => genCtx x >>= fun _ => genCtx y
  | _                  => if !(← get).fst.contains e then modify fun (es, cache) => (es.push e, cache)

partial def toQPolyNormExpr (ctx : Q(PolyNorm.Context)) (es : Array Q(Int)) (e : Q(Int)) (cache : HashMap Expr (Expr × Expr)) :
  MetaM (HashMap Expr (Expr × Expr) × (o : Q(PolyNorm.Expr)) × Q(«$o».denote $ctx = $e)) := do
  match cache.find? e with
  | some (e, h) => return ⟨cache, e, h⟩
  | none   =>
    let ⟨cache, o, h⟩ ← go
    return ⟨cache.insert e (o, h), o, h⟩
where
  go : MetaM (HashMap Expr (Expr × Expr) × (o : Q(PolyNorm.Expr)) × Q(«$o».denote $ctx = $e)) := do match e with
    | ~q(OfNat.ofNat $x) =>
      pure ⟨cache, q(.val (@OfNat.ofNat Int $x _)), q(rfl)⟩
    | ~q(-$x) =>
      let ⟨cache, o, h⟩ ← toQPolyNormExpr ctx es x cache
      pure ⟨cache, q(.neg $o), q(Int.neg_congr $h)⟩
    | ~q($x + $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.add $ox $oy), q(Int.add_congr $hx $hy)⟩
    | ~q($x - $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.sub $ox $oy), q(Int.sub_congr $hx $hy)⟩
    | ~q($x * $y) =>
      let ⟨cache, ox, hx⟩ ← toQPolyNormExpr ctx es x cache
      let ⟨cache, oy, hy⟩ ← toQPolyNormExpr ctx es y cache
      pure ⟨cache, q(.mul $ox $oy), q(Int.mul_congr $hx $hy)⟩
    | _ =>
      let some v := (es.findIdx? (· == e)) | throwError "variable not found"
      pure ⟨cache, q(.var $v), .app q(@Eq.refl Int) e⟩

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (_, (es, _)) ← (genCtx l >>= fun _ => genCtx r).run (#[], {})
  let is : Q(Array Int) ← pure (es.foldl (fun acc e => q(«$acc».push $e)) q(#[]))
  let ctx : Q(PolyNorm.Context) ← pure q((«$is».getD · 0))
  let ⟨cache, el, _⟩ ← toQPolyNormExpr ctx es l {}
  let ⟨_, er, _⟩ ← toQPolyNormExpr ctx es r cache
  let hp : Q(«$el».toPolynomial = «$er».toPolynomial) := (.app q(@Eq.refl PolyNorm.Polynomial) q(«$el».toPolynomial))
  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $el $er $hp)
  mv.assign he
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Int)) := do
    let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (_, (es, _)) ← (genCtx l >>= fun _ => genCtx r).run (#[], {})
  let is : Q(List Int) ← pure (es.foldr (fun e acc => q($e :: $acc)) q([]))
  let ctx : Q(PolyNorm.Context) ← pure q((«$is».getD · 0))
  let ⟨cache, el, _⟩ ← toQPolyNormExpr ctx es l {}
  let ⟨_, er, _⟩ ← toQPolyNormExpr ctx es r cache
  let hp  ← nativeDecide q(«$el».toPolynomial = «$er».toPolynomial)
  let he := q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $el $er $hp)
  mv.assign he
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Int)) := do
    let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
    let ppCtx := (es.getD · q(0))
    logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"
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
    Int.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Int.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Int.Tactic

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  poly_norm

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  native_poly_norm
