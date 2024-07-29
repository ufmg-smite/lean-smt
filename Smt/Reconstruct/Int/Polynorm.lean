/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Qq

namespace Smt.Reconstruct.Int.PolyNorm

abbrev Var := Nat

def Context := Var → Int

structure Monomial where
  mk ::
  coeff : Int
  vars : List Var
deriving Inhabited, Repr

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

theorem eq : ∀ {m n : Monomial}, m.coeff = n.coeff → m.vars = n.vars → m = n
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl




section
variable {op : α → α → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  revert z1 z2
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro z1 z2
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (z1 z2 : α) :
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  revert z1 z2
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro z1 z2
    simp only [List.foldr_cons, ih, assoc]


end
-- Can be generazlized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Int.mul_assoc (ctx y) (ctx x), Int.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Int.mul_comm,
                 foldl_assoc Int.mul_assoc, ih]
      rw [← Int.mul_assoc, Int.mul_comm (ctx x) (ctx y), Int.mul_assoc]

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

theorem foldl_ite {m : Monomial} (g : Var → Int) (hi : i ∈ m.vars) :
  ∃ k : Nat, List.foldl (fun acc v => acc * (if v = i then (g i) else 1)) z m.vars = z * (g i)^k := by
  revert z hi
  induction m.vars with
  | nil => intro z hi; simp at hi
  | cons v l ih =>
    intro z hi
    cases hi with
    | head =>
      simp [foldl_assoc Int.mul_assoc]
      sorry
    | tail _ ha =>
      simp only [List.foldl_cons, Int.one_mul]
      have ⟨k, hk⟩ := @ih (z * if v = i then g i else 1) ha
      rw [hk]
      split
      case inl hv => rw [Int.mul_assoc, Int.mul_comm (g i), ←Int.pow_succ]
                     exact ⟨k + 1, rfl⟩
      case inr _ =>  rw [Int.mul_one]
                     exact ⟨k, rfl⟩


-- theorem denote_eq {m n : Monomial} (h : ∀ ctx : Context, m.denote ctx = n.denote ctx) : m = n := by
--   apply eq
--   · sorry
--   · induction m.vars, n.vars using List.rec with
--     | nil nil => sorry
--     | nil cons a b => sorry
--     | cons a b nil => sorry
--     | cons a b ih cons c d ih1 => sorry




  -- · sorry
  -- · apply List.ext_get
  --   · sorry
  --   · intro i h1 h2;
  --     have h3 := h (fun j => if i = j then i else 1)
  --     simp [denote] at h3
  --     sorry

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

#eval add [⟨5, [0, 1]⟩, ⟨7, [0, 1, 1]⟩] [⟨3, [0, 1, 1]⟩, ⟨2, [0, 1]⟩]
#eval add [⟨3, [0, 1, 1]⟩, ⟨2, [0, 1]⟩] [⟨5, [0, 1]⟩, ⟨7, [0, 1, 1]⟩]


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
    split
    <;> simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]
    case cons.inr h =>
      split
      case inl h1 =>
        split
        case inl h2 =>
          rw [←Int.add_assoc, Int.add_comm, ←Monomial.denote_add h1]
          simp [Monomial.denote, h2]
        case inr h2 =>
          simp [-Int.add_zero, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.denote_add h1, Int.add_assoc]
      case inr h1 =>
        simp only [List.foldl_cons, Int.add_comm 0, ih, Monomial.foldl_assoc Int.add_assoc]
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

-- #check Fin.mk
-- theorem denote_cast {p : List Monomial} :
--   denote ctx (List.foldl f [] p) = List.foldl (fun acc m => denote ctx (f [m] ⟨acc, []⟩)) 0 p := by
--   induction p with
--   | nil => simp [denote]
--   | cons n p ih =>
--     simp only [List.foldl_cons]
--     rw [← Int.add_zero (denote ctx (f [n] ⟨0, []⟩)), Monomial.foldl_assoc Int.add_assoc]

theorem denote_ite {p : Polynomial} : denote (fun j => if j = i then 1 else 0) p = if h : i < p.length then Monomial.denote (fun _ => 1) (p.get ⟨i, h⟩) else 0:= by
  induction p with
  | nil => sorry
  | cons n p ih =>
    split
    case cons.inl h1 =>
      simp only [denote, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.denote]
      sorry
    sorry


#check List.ext_get

theorem denote_eq {p q : Polynomial} (h : ∀ ctx, p.denote ctx = q.denote ctx) : p = q := by
  apply List.ext_get
  · sorry
  · intro i h1 h2
    have h' := h (fun j => if j = i then 1 else 0)
    rw [denote_ite, denote_ite] at h'
    simp [h1, h2, Monomial.denote] at h'
    apply Monomial.eq
    · sorry
    · sorry

theorem add_assoc :∀ (p q r : Polynomial), add (add p q) r = add p (add q r) := by
  intro p q r; simp only [add]; revert p q
  induction r with
  | nil => sorry
  | cons n r ih =>
    intro p q
    induction q with
    | nil => sorry
    | cons => sorry

theorem add_comm : ∀ (p q : Polynomial), add p q = add q p := by
  intro p; simp only [add]
  induction p with
  | nil => sorry
  | cons n p ih =>
    intro q
    simp only [add, add.insert, List.foldr_cons, ih q]
    induction q with
    | nil => unfold add.insert
             simp
             sorry
    | cons => sorry



theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx := by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, Int.add_mul, ← ih]
    rw [denote_foldl]
    rw [denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

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

abbrev PolyM := StateT (Array Q(Int)) MetaM

def getIndex (e : Q(Int)) : PolyM Nat := do
  let es ← get
  if let some i := es.findIdx? (· == e) then
    return i
  else
    let size := es.size
    set (es.push e)
    return size

partial def toPolyNormExpr (e : Q(Int)) : PolyM PolyNorm.Expr := do
  match e with
  | ~q(OfNat.ofNat $x) => pure (.val x.rawNatLit?.get!)
  | ~q(-$x) => pure (.neg (← toPolyNormExpr x))
  | ~q($x + $y) => pure (.add (← toPolyNormExpr x) (← toPolyNormExpr y))
  | ~q($x - $y) => pure (.sub (← toPolyNormExpr x) (← toPolyNormExpr y))
  | ~q($x * $y) => pure (.mul (← toPolyNormExpr x) (← toPolyNormExpr y))
  | e => let v : Nat ← getIndex e; pure (.var v)

partial def toQPolyNormExpr (e : Q(Int)) : PolyM Q(PolyNorm.Expr) := do
  match e with
  | ~q(OfNat.ofNat $x) => pure q(.val (@OfNat.ofNat Int $x _))
  | ~q(-$x) => pure q(.neg $(← toQPolyNormExpr x))
  | ~q($x + $y) => pure q(.add $(← toQPolyNormExpr x) $(← toQPolyNormExpr y))
  | ~q($x - $y) => pure q(.sub $(← toQPolyNormExpr x) $(← toQPolyNormExpr y))
  | ~q($x * $y) => pure q(.mul $(← toQPolyNormExpr x) $(← toQPolyNormExpr y))
  | e => let v : Nat ← getIndex e; pure q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, es) ← (toQPolyNormExpr l).run #[]
  let (r, es) ← (toQPolyNormExpr r).run es
  let is : Q(Array Int) := es.foldl (fun acc e => q(«$acc».push $e)) q(#[])
  let ctx : Q(PolyNorm.Context) := q(fun v => if h : v < «$is».size then $is[v] else 0)
  let h : Q(«$l».toPolynomial = «$r».toPolynomial) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPolynomial)
  mv.assign q(@PolyNorm.Expr.denote_eq_from_toPolynomial_eq $ctx $l $r $h)
where
  logPolynomial (e : Q(PolyNorm.Expr)) (es : Array Q(Int)) := do
  let p ← unsafe Meta.evalExpr PolyNorm.Expr q(PolyNorm.Expr) e
  let ppCtx := fun v => if h : v < es.size then es[v] else q(0)
  logInfo m!"poly := {PolyNorm.Polynomial.toExpr p.toPolynomial ppCtx}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Int.polyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Int.Tactic

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  poly_norm
