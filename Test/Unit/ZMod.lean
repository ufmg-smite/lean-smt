import Smt
import Smt.ZMod
import Smt.Reconstruct.ZMod.Polynorm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nullstellensatz

open Lean in
private def Lean.RArray.toExpr' (lvl : Level) (ty : Expr) (f : α → Expr) (a : RArray α) : Expr :=
  let leaf := mkConst ``RArray.leaf [lvl]
  let branch := mkConst ``RArray.branch [lvl]
  let rec go (a : RArray α) : Expr :=
    match a with
    | .leaf x  =>
      mkApp2 leaf ty (f x)
    | .branch p l r =>
      mkApp4 branch ty (mkRawNatLit p) (go l) (go r)
  go a

def Lean.Expr.mvarId? : Expr → Option MVarId
  | mvar n => some n
  | _      => none

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

def addN [AddMonoid A] : List A → A
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append [AddMonoid A] {xs ys : List A}
  : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, add_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem addN_cons_append [AddMonoid A] {x : A}
  : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, add_zero]

namespace Smt.Reconstruct.ZMod

prefix:75 "-ₚ"   => Expr.neg
infixl:65 " +ₚ " => Expr.add
infixl:70 " *ₚ " => Expr.mul

@[app_unexpander Expr.val]
def unexpandZModExprConst : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => ``($x)
  | _ => throw ()

namespace Expr

noncomputable def toPoly : Expr n → MvPolynomial Nat (ZMod n)
  | .var i => .X i
  | .val c => .C c
  | .add a b => toPoly a + toPoly b
  | .sub a b => toPoly a - toPoly b
  | .mul a b => toPoly a * toPoly b
  | .neg a => -toPoly a

@[simp] theorem eval_toPoly (ctx : Nat → ZMod n) (e : Expr n) :
  MvPolynomial.eval ctx e.toPoly = e.eval ctx := by
  induction e <;> simp [toPoly, eval, *]

@[simp] theorem aeval_toPoly (ctx : Nat → ZMod n) (e : Expr n) :
  MvPolynomial.aeval ctx e.toPoly = e.eval ctx := by
  simp [MvPolynomial.aeval_eq_eval]

open Qq Lean

abbrev ZModExprM (_n : Nat) := ReconstructM

def getIndex (n : Nat) (e : Q(ZMod $n)) : ZModExprM n Nat := do
  let is ← getFFCtx n
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    setFFCtx n (is.push e)
    return size

partial def reify (n : Nat) (e : Q(ZMod $n)) : ZModExprM n (Q(Expr $n)) := do
  if let some _ := e.natLitOf? q(ZMod $n) then
    return q(val $e)
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

end Expr

open Lean Qq

abbrev MvPolynomialM (_n : Nat) := ReconstructM

namespace MvPolynomialM

def getIndex (n : Nat) (e : Q(ZMod $n)) : MvPolynomialM n Nat := do
  let is ← getFFCtx n
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    setFFCtx n (is.push e)
    return size

partial def reify (n : Nat) (e : Q(ZMod $n)) : MvPolynomialM n (Q(MvPolynomial Nat (ZMod $n))) := do
  if let some _ := e.natLitOf? q(ZMod $n) then
    return q(.C $e)
  else if let some e' := e.negOf? q(ZMod $n) then
    return q(-$(← reify n e'))
  else if let some (x, y) := e.hAddOf? q(ZMod $n) q(ZMod $n) then
    return q($(← reify n x) + $(← reify n y))
  else if let some (x, y) := e.hSubOf? q(ZMod $n) q(ZMod $n) then
    return q($(← reify n x) - $(← reify n y))
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

noncomputable
def Monomial.toMvPoly {n : Nat} (m : Monomial n) :
    MvPolynomial Nat (ZMod n) :=
  MvPolynomial.C m.coeff *
    m.vars.foldl (fun acc v => acc * MvPolynomial.X v) 1

noncomputable
def Polynomial.toMvPoly {n : Nat} (p : Polynomial n) :
    MvPolynomial Nat (ZMod n) :=
  p.foldl (fun acc m => acc + m.toMvPoly) 0

@[simp] lemma Monomial.toMvPoly_neg {n : Nat} (m : Monomial n) :
    m.neg.toMvPoly = -m.toMvPoly := by
  simp [Monomial.toMvPoly, Monomial.neg, neg_mul]

@[simp] lemma Monomial.toMvPoly_add {n : Nat} {m₁ m₂ : Monomial n}
    (h : m₁.vars = m₂.vars) :
    (m₁.add m₂ h).toMvPoly = m₁.toMvPoly + m₂.toMvPoly := by
  simp [Monomial.toMvPoly, Monomial.add, h, add_mul]

@[simp] lemma Polynomial.toMvPoly_nil {n : Nat} :
    Polynomial.toMvPoly ([] : Polynomial n) = 0 := by
  simp [Polynomial.toMvPoly]

@[simp] lemma Polynomial.toMvPoly_cons {n : Nat} (m : Monomial n) (p : Polynomial n) :
    Polynomial.toMvPoly (m :: p) = m.toMvPoly + Polynomial.toMvPoly p := by
  simp [Polynomial.toMvPoly]
  simpa using
    (Monomial.foldl_assoc
      (op := (· + ·))
      (g := fun m : Monomial n => m.toMvPoly)
      (l := p)
      add_assoc
      m.toMvPoly
      0)

def Expr.isUnivariateOver {n : Nat} (p : Expr n) (i : Nat) : Bool :=
  go i p
where
  go (i : Nat) : Expr n → Bool
    | .var i'  => i' == i
    | .val _   => true
    | .add a b => go i a && go i b
    | .sub a b => go i a && go i b
    | .mul a b => go i a && go i b
    | .neg a   => go i a

def Expr.gcd {n : Nat} (p q : Expr n) : Expr n :=
  let i := (findVar p <|> findVar q).getD 0
  let pc := toCoeffs p.toPolynomial
  let qc := toCoeffs q.toPolynomial
  let gc := euclidGcd pc qc (pc.length + qc.length + 1)
  toExpr i gc
where
  findVar : Expr n → Option Nat
    | .var i    => some i
    | .neg a    => findVar a
    | .add a b  => findVar a <|> findVar b
    | .sub a b  => findVar a <|> findVar b
    | .mul a b  => findVar a <|> findVar b
    | .val _    => none
  trim (cs : List (ZMod n)) : List (ZMod n) :=
    cs.reverse.dropWhile (· == 0) |>.reverse
  toCoeffs (p : Polynomial n) : List (ZMod n) :=
    let deg := p.foldl (fun d (m : Monomial n) => max d m.vars.length) 0
    let arr := Array.replicate (deg + 1) (0 : ZMod n)
    let arr := p.foldl (fun arr (m : Monomial n) => arr.modify m.vars.length (· + m.coeff)) arr
    trim arr.toList
  pseudoRem (a b : List (ZMod n)) (fuel : Nat) : List (ZMod n) :=
    match fuel with
    | 0 => a
    | fuel + 1 =>
      match b with
      | [] => a
      | _ =>
        if a.length < b.length then a
        else
          let lca := a.getLast!
          let lcb := b.getLast!
          let shift := a.length - b.length
          let a' := a.map (· * lcb)
          let bShifted := List.replicate shift 0 ++ b.map (· * lca)
          let r := trim (List.zipWith (· - ·) a' bShifted)
          pseudoRem r b fuel
  euclidGcd (a b : List (ZMod n)) (fuel : Nat) : List (ZMod n) :=
    match fuel with
    | 0 => a
    | fuel + 1 =>
      match b with
      | [] => a
      | _ => euclidGcd b (pseudoRem a b (a.length + 1)) fuel
  toExpr (i : Nat) (cs : List (ZMod n)) : Expr n :=
    match cs.reverse with
    | []      => .val 0
    | c :: cs => cs.foldl (fun acc coeff => .add (.val coeff) (.mul (.var i) acc)) (.val c)

def Expr.pow {n : Nat} (p : Expr n) : Nat → Expr n
  | 0     => .val 1
  | k + 1 => p.mul (p.pow k)

instance : Neg (Expr n) where
  neg := Expr.neg

instance : Add (Expr n) where
  add := Expr.add

instance : Sub (Expr n) where
  sub := Expr.sub

instance : Mul (Expr n) where
  mul := Expr.mul

instance : Pow (Expr n) Nat where
  pow := Expr.pow

def Expr.deg (p : Expr n) (i : Nat) : Nat :=
  match p with
  | .var i'  => if i' == i then 1 else 0
  | .val _   => 0
  | .add a b => max (a.deg i) (b.deg i)
  | .sub a b => max (a.deg i) (b.deg i)
  | .mul a b => a.deg i + b.deg i
  | .neg a   => a.deg i

-- TODO(all): simplify this definition as much as possible to make Liza's life easier!
def Expr.completeRoots (p : Expr n) (i : Nat) (rs : List (ZMod n)) : Bool :=
  p.isUnivariateOver i &&
  rs.eraseDups == rs &&
  rs.all (fun z => p.eval (fun _ => z) == 0) &&
  (Expr.gcd p (.var i ^ n - .var i)).deg i == rs.length

theorem roots_complete [Fact n.Prime] {p : Expr n}
  (h : p.completeRoots i rs) : ∀ r ∉ rs, p.eval (fun _ => r) ≠ 0 := by
  sorry

theorem root_branch [Fact n.Prime] {ps} {p : Expr n} {i rs}
  (hps : variety (ideal ps) ≠ ∅) (hp : p.toPoly ∈ ideal ps)
  (hpirs : p.completeRoots i rs)
  : orN (rs.map fun r => variety (ideal (ps ++ [.X i - .C r])) ≠ ∅) := by
  sorry

@[simp] theorem Polynomial.toMvPoly_neg {n : Nat} (p : Polynomial n) :
    Polynomial.toMvPoly (Polynomial.neg p) = -Polynomial.toMvPoly p := by
  induction p with
  | nil =>
      simp [Polynomial.neg, Polynomial.toMvPoly]
  | cons m ms ih =>
      rw [show Polynomial.neg (m :: ms) = Monomial.neg m :: Polynomial.neg ms by rfl]
      rw [Polynomial.toMvPoly_cons, Polynomial.toMvPoly_cons, Monomial.toMvPoly_neg, ih]
      rw [neg_add]

theorem Polynomial.toMvPoly_add_insert {n : Nat} (m : Monomial n) (p : Polynomial n) :
    Polynomial.toMvPoly (Polynomial.add.insert m p) = m.toMvPoly + Polynomial.toMvPoly p := by
  induction p with
  | nil =>
      simp [Polynomial.add.insert, Polynomial.toMvPoly_cons]
  | cons n p ih =>
      by_cases hlt : m.vars < n.vars
      · simp [Polynomial.add.insert, hlt, Polynomial.toMvPoly_cons]
      · simp [Polynomial.add.insert, hlt]
        by_cases heq : m.vars = n.vars
        · simp [heq]
          by_cases hzero : (m.add n heq).coeff = 0
          · simp [hzero]
            have hmadd0 : (m.add n heq).toMvPoly = 0 := by
              simp [Monomial.toMvPoly, Monomial.add]
              have hcoeff : m.coeff + n.coeff = 0 := by
                   simpa [Monomial.add] using hzero
              rw [← MvPolynomial.C_add]
              rw [hcoeff]
              simp
            have hsum : m.toMvPoly + n.toMvPoly = 0 := by
              simpa [Monomial.toMvPoly_add, heq] using hmadd0
            rw [← add_assoc, hsum]
            simp
          · simp [hzero, Polynomial.toMvPoly_cons, Monomial.toMvPoly_add,
                  add_assoc]
        · simp [heq]
          simp [ih]
          simp [ add_left_comm]


@[simp] theorem Polynomial.toMvPoly_add {n : Nat} (p q : Polynomial n) :
    Polynomial.toMvPoly (Polynomial.add p q) =
      Polynomial.toMvPoly p + Polynomial.toMvPoly q := by
  induction p with
  | nil =>
      simp [Polynomial.add, Polynomial.toMvPoly]
  | cons x ys ih =>
      rw [show Polynomial.add (x :: ys) q = Polynomial.add.insert x (Polynomial.add ys q) by rfl]
      rw [Polynomial.toMvPoly_add_insert]
      rw [ih]
      simp [Polynomial.toMvPoly_cons, add_left_comm, add_comm]


@[simp] theorem Monomial.toMvPoly_mul {n : Nat} {m₁ m₂ : Monomial n} :
    (m₁.mul m₂).toMvPoly = m₁.toMvPoly * m₂.toMvPoly := by
  simp [Monomial.toMvPoly, Monomial.mul, mul_assoc, mul_left_comm]
  apply congrArg (fun t =>
    MvPolynomial.C m₁.coeff * (MvPolynomial.C m₂.coeff * t))
  have hinsert :
      ∀ (y : Var) (ys : List Var),
        List.foldl
            (fun (acc : MvPolynomial Nat (ZMod n)) (v : Var) => acc * MvPolynomial.X v)
            (1 : MvPolynomial Nat (ZMod n))
            (Monomial.mul.insert y ys)
          =
        (MvPolynomial.X y : MvPolynomial Nat (ZMod n)) *
          List.foldl
            (fun (acc : MvPolynomial Nat (ZMod n)) (v : Var) => acc * MvPolynomial.X v)
            (1 : MvPolynomial Nat (ZMod n))
            ys := by
    intro y ys
    induction ys with
    | nil =>
        simp [Monomial.mul.insert]
    | cons x ys ih =>
        by_cases h : y ≤ x
        · simp [Monomial.mul.insert, h]
          simpa using
            (Monomial.foldl_assoc
              (op := (· * ·))
              (g := fun v : Var => (MvPolynomial.X v : MvPolynomial Nat (ZMod n)))
              (l := ys)
              mul_assoc
              (MvPolynomial.X y)
              (MvPolynomial.X x))
        · simp [Monomial.mul.insert, h]
          have hleft :
              List.foldl (fun acc v => acc * MvPolynomial.X v) (MvPolynomial.X x) (Monomial.mul.insert y ys)
                =
              (MvPolynomial.X x : MvPolynomial Nat (ZMod n)) *
                List.foldl (fun acc v => acc * MvPolynomial.X v) 1 (Monomial.mul.insert y ys) := by
            simpa using
              (Monomial.foldl_assoc
                (op := (· * ·))
                (g := fun v : Var => (MvPolynomial.X v : MvPolynomial Nat (ZMod n)))
                (l := Monomial.mul.insert y ys)
                mul_assoc
                (MvPolynomial.X x)
                (1 : MvPolynomial Nat (ZMod n)))

          have hright :
              List.foldl (fun acc v => acc * MvPolynomial.X v) (MvPolynomial.X x) ys
                =
              (MvPolynomial.X x : MvPolynomial Nat (ZMod n)) *
                List.foldl (fun acc v => acc * MvPolynomial.X v) 1 ys := by
            simpa using
              (Monomial.foldl_assoc
                (op := (· * ·))
                (g := fun v : Var => (MvPolynomial.X v : MvPolynomial Nat (ZMod n)))
                (l := ys)
                mul_assoc
                (MvPolynomial.X x)
                (1 : MvPolynomial Nat (ZMod n)))
          rw [hleft, ih, hright]
          rw [<- mul_assoc]
          rw [mul_comm (MvPolynomial.X x) (MvPolynomial.X y)]
          rw [← mul_assoc]
  induction m₁.vars with
  | nil =>
      simp
  | cons y ys ih =>
      have hins :
          List.foldl
              (fun (acc : MvPolynomial Nat (ZMod n)) (v : Var) => acc * MvPolynomial.X v)
              (1 : MvPolynomial Nat (ZMod n))
              (Monomial.mul.insert y (List.foldr Monomial.mul.insert m₂.vars ys))
            =
          (MvPolynomial.X y : MvPolynomial Nat (ZMod n)) *
            List.foldl
              (fun (acc : MvPolynomial Nat (ZMod n)) (v : Var) => acc * MvPolynomial.X v)
              (1 : MvPolynomial Nat (ZMod n))
              (List.foldr Monomial.mul.insert m₂.vars ys) := by
        simpa using hinsert y (List.foldr Monomial.mul.insert m₂.vars ys)
      simp [hins]
      rw [ih]

      have hfold :
    (MvPolynomial.X y : MvPolynomial Nat (ZMod n)) *
      List.foldl (fun acc v => acc * MvPolynomial.X v) 1 ys
    =
    List.foldl (fun acc v => acc * MvPolynomial.X v) (MvPolynomial.X y) ys := by
        simpa using
          (Monomial.foldl_assoc
            (op := (· * ·))
            (g := fun v : Var => (MvPolynomial.X v : MvPolynomial Nat (ZMod n)))
            (l := ys)
            mul_assoc
            (MvPolynomial.X y)
            (1 : MvPolynomial Nat (ZMod n))).symm
      calc
        (MvPolynomial.X y : MvPolynomial Nat (ZMod n)) *
            (List.foldl (fun acc v => acc * MvPolynomial.X v) 1 ys *
              List.foldl (fun acc v => acc * MvPolynomial.X v) 1 m₂.vars)
            =
          ((MvPolynomial.X y : MvPolynomial Nat (ZMod n)) *
            List.foldl (fun acc v => acc * MvPolynomial.X v) 1 ys) *
              List.foldl (fun acc v => acc * MvPolynomial.X v) 1 m₂.vars := by
                simp [mul_assoc]
        _ =
          List.foldl (fun acc v => acc * MvPolynomial.X v) (MvPolynomial.X y) ys *
            List.foldl (fun acc v => acc * MvPolynomial.X v) 1 m₂.vars := by
              exact congrArg
                (fun t =>
                  t * List.foldl (fun acc v => acc * MvPolynomial.X v) 1 m₂.vars)
                hfold



@[simp] theorem Polynomial.toMvPoly_mulMonomial {n : Nat} {m : Monomial n} {p : Polynomial n} :
  Polynomial.toMvPoly (Polynomial.mulMonomial m p) = m.toMvPoly * Polynomial.toMvPoly p := by
  simp only [Polynomial.mulMonomial]
  induction p with
  | nil =>
      simp [Polynomial.toMvPoly]
  | cons n p ih =>
      simp [Polynomial.toMvPoly_add, Monomial.toMvPoly_mul]
      rw [ih]
      simp [mul_add]

@[simp] theorem Polynomial.toMvPoly_nil_add {n : Nat} {p : Polynomial n} :
  Polynomial.toMvPoly (p.add []) = Polynomial.toMvPoly p := by
  simp


theorem Polynomial.toMvPoly_add_insert_foldl {o : Nat} {g : Monomial o → Polynomial o}
    (p : Polynomial o) (n : Polynomial o) :
  Polynomial.toMvPoly (List.foldl (fun acc m => (g m).add acc) n p) =
    Polynomial.toMvPoly n +
      Polynomial.toMvPoly (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil =>
      simp [Polynomial.toMvPoly]
  | cons k p ih =>
      intro n
      simp only [List.foldl_cons]
      rw [ih, @ih ((g k).add []), ← add_assoc, Polynomial.toMvPoly_nil_add,
          Polynomial.toMvPoly_add, add_comm _ (Polynomial.toMvPoly n)]

theorem Polynomial.toMvPoly_foldl {o : Nat} {g : Monomial o → Polynomial o}
    (p : Polynomial o) :
  Polynomial.toMvPoly (List.foldl (fun acc m => (g m).add acc) [] p) =
    List.foldl (fun acc m => Polynomial.toMvPoly (g m) + acc) 0 p := by
  induction p with
  | nil =>
      simp [Polynomial.toMvPoly]
  | cons n p ih =>
      simp only [List.foldl_cons, add_comm] at *
      rw [add_comm (0 : MvPolynomial Nat (ZMod o)),
          Monomial.foldl_assoc add_assoc, ← ih,
          Polynomial.toMvPoly_add_insert_foldl,
          Polynomial.toMvPoly_nil_add]

@[simp] theorem Polynomial.toMvPoly_mul {n : Nat} (p q : Polynomial n) :
    Polynomial.toMvPoly (Polynomial.mul p q) =
      Polynomial.toMvPoly p * Polynomial.toMvPoly q := by
  simp only [Polynomial.mul]
  induction p with
  | nil =>
      simp [Polynomial.toMvPoly]
  | cons x ys ih =>
      simp only [List.foldl_cons, Polynomial.toMvPoly_cons, add_mul, ← ih]
      rw [Polynomial.toMvPoly_foldl,
          Polynomial.toMvPoly_add_insert_foldl,
          ← Polynomial.toMvPoly_mulMonomial,
          Polynomial.toMvPoly_nil_add,
          Polynomial.toMvPoly_foldl]


@[simp] theorem Polynomial.toMvPoly_sub {n : Nat} (p q : Polynomial n) :
    Polynomial.toMvPoly (Polynomial.sub p q) =
      Polynomial.toMvPoly p - Polynomial.toMvPoly q := by
  simp [Polynomial.sub, sub_eq_add_neg]

lemma Expr.toPoly_eq_toMvPoly_toPolynomial (e : Expr n) :
  Polynomial.toMvPoly e.toPolynomial = e.toPoly := by
  induction e with
  | val v =>
      simp [Expr.toPolynomial, Expr.toPoly, Polynomial.toMvPoly, Monomial.toMvPoly]
      split
      · rename_i hv
        simp [hv]
      · rename_i hv
        simp
  | var v =>
      simp [Expr.toPolynomial, Expr.toPoly, Polynomial.toMvPoly, Monomial.toMvPoly]
  | neg a ih =>
      simpa [Expr.toPolynomial, Expr.toPoly] using congrArg Neg.neg ih
  | add a b iha ihb =>
      simp [Expr.toPolynomial, Expr.toPoly, iha, ihb]
  | sub a b iha ihb =>
      simp [Expr.toPolynomial, Expr.toPoly, iha, ihb]
  | mul a b iha ihb =>
       simp [Expr.toPolynomial, Expr.toPoly, iha, ihb]

theorem Expr.toPoly_eq_of_toPolynomial_eq
    {e₁ e₂ : Expr n}
    (he : e₁.toPolynomial = e₂.toPolynomial) :
    e₁.toPoly = e₂.toPoly := by
  have h := congrArg Polynomial.toMvPoly he
  simpa [Expr.toPoly_eq_toMvPoly_toPolynomial] using h

-- -- TODO(Liza): prove the correctness of this lemma!
theorem Expr.elem_congr {e₁ e₂ : Expr n} {s₁ s₂ : Ideal (MvPolynomial Nat (ZMod n))}
  (he : e₁.toPolynomial = e₂.toPolynomial) (hs : s₁ = s₂) :
  (e₁.toPoly ∈ s₁) = (e₂.toPoly ∈ s₂) := by
   subst hs
   rw [Expr.toPoly_eq_of_toPolynomial_eq he]


theorem Expr.variety_nonempty_of_eval_eq_zero [Fact n.Prime] {es : List (Expr n)}
  (h : andN (es.map fun e => e.eval ctx = 0)) :
  variety (ideal (es.map toPoly)) ≠ ∅ := by
  have hall : ∀ e ∈ es, e.eval ctx = 0 := by
    induction es with
    | nil =>
        intro e he
        cases he
    | cons e es ih =>
        simp only [List.map, andN_cons_append] at h
        rcases h with ⟨he, hes⟩
        intro e' he'
        simp only [List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact he
        · exact ih hes _ he'
  exact Set.nonempty_iff_ne_empty.mp ⟨ctx, by
    rw [variety, ideal, MvPolynomial.zeroLocus_span]
    intro p hp
    rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨e, he, rfl⟩
    simpa using hall e he
  ⟩

theorem poly_combination (ps ms rs : List (MvPolynomial Nat (ZMod n)))
  (h : andN (rs.map fun r => r ∈ ideal ps))
  : addN (List.zipWith (· * ·) ms rs) ∈ ideal ps := by
  induction ms generalizing rs with
  | nil =>
    simp [List.zipWith, addN, ideal]
  | cons m ms ih =>
    cases rs with
    | nil =>
      simp [List.zipWith, addN, ideal]
    | cons r rs =>
      simp only [List.map, andN_cons_append] at h
      rcases h with ⟨hr, hrs⟩
      simp [List.zipWith, addN_cons_append]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hr) (ih rs hrs)

theorem diseq' [Fact n.Prime] {l r : ZMod n}
  : (l ≠ r) = (∃ k, (l + -r) * k + -1 = 0) := by
  grind

theorem diseq [Fact n.Prime] {l r : ZMod n}
  : (l ≠ r) = ((l + -r) * Classical.epsilon (fun x => (l + -r) * x + -1 = 0) + -1 = 0) := by
  rewrite [diseq']
  apply propext
  constructor
  · apply Classical.epsilon_spec_aux (p := fun x => (l + -r) * x + -1 = 0)
  · intro h
    exists (Classical.epsilon (fun x => (l + -r) * x + -1 = 0))

theorem eq_of_add_neg_eq [Fact n.Prime] {c₁ c₂ : ZMod n}
  (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ + -a₂) = c₂ * (b₁ + -b₂))
  : (a₁ = a₂) = (b₁ = b₂) := by
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
    rightAssocOp q(@HAdd.hAdd (ZMod $w) (ZMod $w) (ZMod $w) _) t
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
    for i in t.getChildren.reverse do
      let p : Q(ZMod $o) ← reconstructTerm i
      let p ← MvPolynomialM.reify o p
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
    let x ← MvPolynomialM.reify o x
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
      return q(Classical.epsilon (fun x => ($a + -$b) * x + -1 = 0))
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
  leftAssocOp (op : Lean.Expr) (t : cvc5.Term) : ReconstructM Lean.Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr
  rightAssocOp (op : Lean.Expr) (t : cvc5.Term) : ReconstructM Lean.Expr := do
    let (ts, [t]) := t.getChildren.toList.splitAt (t.getNumChildren - 1)
      | throwError "unexpected number of children in right-associative operator: {t.getNumChildren}, expected at least 1"
    ts.foldrM (fun t acc => return mkApp2 op (← reconstructTerm t) acc) (← reconstructTerm t)

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Lean.Expr) := do
  match pf.getRewriteRule! with
  | _ => return none

open Qq

@[smt_proof_reconstruct] def reconstructFfProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .REFL =>
    if pf.getArguments[0]!.getKind != .FINITE_FIELD_IDEAL then return none
    let o : Nat := pf.getArguments[0]!.getSort.getSetElementSort!.getFiniteFieldSize!
    let a : Q(Ideal (MvPolynomial Nat (ZMod $o))) ← reconstructTerm pf.getArguments[0]!
    addThm q($a = $a) q(Eq.refl $a)
  | .CONG =>
    if pf.getResult[0]!.getKind != .SET_MEMBER || (pf.getResult[0]!)[1]!.getKind != .FINITE_FIELD_IDEAL then
      return none
    let o : Nat ← pure (pf.getResult[0]!)[0]!.getSort.getFiniteFieldSize!
    let e₁ : Q(ZMod $o) ← reconstructTerm (pf.getResult[0]!)[0]!
    let e₂ : Q(ZMod $o) ← reconstructTerm (pf.getResult[1]!)[0]!
    let e₁ ← Expr.reify o e₁
    let e₂ ← Expr.reify o e₂
    let is ← getFFCtx o
    let ctx : Q(Nat → ZMod $o) ← pure (if h : 0 < is.size
      then let is : Q(RArray (ZMod $o)) := (RArray.ofArray is h).toExpr' 0 q(ZMod $o) id; q(«$is».get)
      else q(fun _ => 0))
    let s₁ : Q(Ideal (MvPolynomial Nat (ZMod $o))) ← reconstructTerm (pf.getResult[0]!)[1]!
    let s₂ : Q(Ideal (MvPolynomial Nat (ZMod $o))) ← reconstructTerm (pf.getResult[1]!)[1]!
    let he : Q(«$e₁».eval $ctx = «$e₂».eval $ctx) ← reconstructProof pf.getChildren[0]!
    let some he ← he.mvarId?.bindM getExprMVarAssignment?
      | throwError "unexpected proof of equality between expressions: {he}, {repr he}"
    let (``Expr.denote_eq_from_toPolynomial_eq, #[_, _, _, _, (he :  Q(«$e₁».toPolynomial = «$e₂».toPolynomial))]) :=
      he.getAppFnArgs | throwError "unexpected proof of equality between expressions: {he}, {repr he}"
    let hs : Q($s₁ = $s₂) ← reconstructProof pf.getChildren[1]!
    addThm q((«$e₁».toPoly ∈ $s₁) = («$e₂».toPoly ∈ $s₂)) q(Expr.elem_congr $he $hs)
  | .FF_POLY_CONVERSION =>
    let ps := ((pf.getResult[0]!)[0]!)[0]!.getChildren
    let o : Nat ← pure ps[0]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let reconstructZMEs := fun (t : cvc5.Term) (acc : Q(List (Expr $o))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let p ← Expr.reify o p
      return q($p :: $acc)
    let ps ← ps.foldrM reconstructZMEs q([])
    let is ← getFFCtx o
    let ctx : Q(Nat → ZMod $o) ← pure (if h : 0 < is.size
      then let is : Q(RArray (ZMod $o)) := (RArray.ofArray is h).toExpr' 0 q(ZMod $o) id; q(«$is».get)
      else q(fun _ => 0))
    let h : Q(andN («$ps».map fun p => p.eval $ctx = 0)) ← reconstructProof pf.getChildren[0]!
    addThm q(variety (ideal («$ps».map Expr.toPoly)) ≠ ∅) q(@Expr.variety_nonempty_of_eval_eq_zero $o $ctx $ho $ps $h)
  | .FF_POLY_NORM =>
    let o : Nat := pf.getResult[0]!.getSort.getFiniteFieldSize!
    let a : Q(ZMod $o) ← reconstructTerm pf.getResult[0]!
    let b : Q(ZMod $o) ← reconstructTerm pf.getResult[1]!
    let l : Q(Expr $o) ← Expr.reify o a
    let r : Q(Expr $o) ← Expr.reify o b
    let is ← getFFCtx o
    let tac := if ← useNative then ZMod.nativePolyNorm o l r is else ZMod.polyNorm o l r is
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
    let y ← MvPolynomialM.reify o y
    let ps := pf.getResult[1]!.getChildren
    let [xs, zs] := ps.toList.splitOn pf.getResult[0]!
      | throwError "unexpected number of generators in ideal: {ps.size}, expected at least 1"
    let reconstructMVPs := fun (t : cvc5.Term) (acc : Q(List (MvPolynomial Nat (ZMod $o)))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let p ← MvPolynomialM.reify o p
      return q($p :: $acc)
    let xs ← xs.foldrM reconstructMVPs q([])
    let zs ← zs.foldrM reconstructMVPs q([])
    addThm q($y ∈ ideal ($xs ++ $y :: $zs)) q(@ideal_generator $o $xs $y $zs)
  | .FF_ONE_UNSAT =>
    let o : Nat := pf.getChildren[0]!.getResult[0]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let ps := pf.getChildren[0]!.getResult[1]!.getChildren
    let reconstructMVPs := fun (t : cvc5.Term) (acc : Q(List (MvPolynomial Nat (ZMod $o)))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let p ← MvPolynomialM.reify o p
      return q($p :: $acc)
    let ps ← ps.foldrM reconstructMVPs q([])
    let h : Q(1 ∈ ideal $ps) ← reconstructProof pf.getChildren[0]!
    addThm q(variety (ideal $ps) = ∅) q(@one_unsat $o $ho $ps $h)
  | .FF_DISEQ =>
    let o : Nat := pf.getArguments[0]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let l : Q(ZMod $o) ← reconstructTerm pf.getArguments[0]!
    let r : Q(ZMod $o) ← reconstructTerm pf.getArguments[1]!
    addThm q(($l ≠ $r) = (($l + -$r) * Classical.epsilon (fun x => ($l + -$r) * x + -1 = 0) + -1 = 0)) q(@diseq $o $ho $l $r)
  | .FF_POLY_COMBINATION =>
    let o : Nat := pf.getResult[0]!.getSort.getFiniteFieldSize!
    let reconstructMVPs := fun (t : cvc5.Term) (acc : Q(List (MvPolynomial Nat (ZMod $o)))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let p ← MvPolynomialM.reify o p
      return q($p :: $acc)
    let ps := pf.getResult[1]!.getChildren
    let ps ← ps.foldrM reconstructMVPs q([])
    let rs := pf.getArguments[0]!.getChildren
    let rs ← rs.foldrM reconstructMVPs q([])
    let ms := pf.getArguments[1]!.getChildren
    let ms ← ms.foldrM reconstructMVPs q([])
    let cpfs := pf.getChildren
    let q : Q(Prop) ← reconstructTerm cpfs.back!.getResult
    let hq : Q($q) ← reconstructProof cpfs.back!
    let f := fun pf ⟨q, hq⟩ => do
      let p : Q(Prop) ← reconstructTerm pf.getResult
      let hp : Q($p) ← reconstructProof pf
      return ⟨q($p ∧ $q), q(And.intro $hp $hq)⟩
    let ⟨_, hq⟩ ← cpfs.pop.foldrM f (⟨q, hq⟩ : Σ q : Q(Prop), Q($q))
    let h : Q(andN (List.map (fun r => r ∈ ideal $ps) $rs)) := hq
    addThm q(addN (List.zipWith (· * ·) $ms $rs) ∈ ideal $ps) q(@poly_combination $o $ps $ms $rs $h)
  | .FF_ROOT_BRANCH =>
    let o : Nat := pf.getArguments[2]!.getSort.getFiniteFieldSize!
    let ho : Q(Fact «$o».Prime) ← Meta.synthInstance q(Fact «$o».Prime)
    let reconstructMVPs := fun (t : cvc5.Term) (acc : Q(List (MvPolynomial Nat (ZMod $o)))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      let p ← MvPolynomialM.reify o p
      return q($p :: $acc)
    let reconstructZMods := fun (t : cvc5.Term) (acc : Q(List (ZMod $o))) => do
      let p : Q(ZMod $o) ← reconstructTerm t
      return q($p :: $acc)
    let ps := (pf.getArguments[1]!).getChildren
    let ps ← ps.foldrM reconstructMVPs q([])
    let p : Q(ZMod $o) ← reconstructTerm pf.getArguments[4]!
    let p ← Expr.reify o p
    let is ← getFFCtx o
    let x : Q(ZMod $o) ← reconstructTerm pf.getArguments[2]!
    let i : Nat := is.findIdx (· == x)
    let rs := pf.getArguments[3]!.getChildren
    let rs ← rs.foldrM reconstructZMods q([])
    let hps : Q(variety (ideal $ps) ≠ ∅) ← reconstructProof pf.getChildren[0]!
    let hp : Q(«$p».toPoly ∈ ideal $ps) ← reconstructProof pf.getChildren[1]!
    let tac := if ← useNative then decide else nativeDecide
    let hpirs : Q(«$p».completeRoots $i $rs) ← tac q(«$p».completeRoots $i $rs)
    addThm q(orN («$rs».map fun r => variety (ideal ($ps ++ [.X $i - .C r])) ≠ ∅))
           q(@root_branch $o $ho $ps $p $i $rs $hps $hp $hpirs)
  | _ => return none
where
  decide (p : Q(Prop)) : MetaM (Q($p)) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    return .app q(@of_decide_eq_true $p $hp) q(Eq.refl true)
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Lean.Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxDeclName baseName
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

end Smt.Reconstruct.ZMod

open Smt.Reconstruct.ZMod
open MvPolynomial Expr

-- set_option trace.smt true
-- set_option trace.smt.reconstruct.proof true
-- set_option trace.smt.solve true
-- set_option pp.instantiateMVars false

example (x: ZMod 3) : x* (x-1)* (x-2) ≠ 1 := by
  smt

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
