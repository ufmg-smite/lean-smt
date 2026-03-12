import Lean

import Smt.Reconstruct.Real.CAD.CPolynomial
import Smt.Reconstruct.Real.CAD.NormalizePoly

open Qq Lean Elab Tactic Meta

open CompPoly
open CPolynomial

def get_lhs (ineq : Expr) : Expr :=
  match ineq with
  | .app (.app (.app (.app (.const `LT.lt ..) _) _) lhs) _ => lhs
  | .app (.app (.app (.app (.const `LE.le ..) _) _) lhs) _ => lhs
  | .app (.app (.app (.app (.const `GT.gt ..) _) _) lhs) _ => lhs
  | .app (.app (.app (.app (.const `GE.ge ..) _) _) lhs) _ => lhs
  | .app (.app (.app (.const ``Eq ..) _) lhs) _ => lhs
  | _ => panic! "[all_to_lhs]: impossible"

partial def get_monoms (e : Q(Real)) : MetaM (List (Q(Real) × Bool)) := do
  match e with
  | ~q(@HAdd.hAdd Real Real Real _ $lhs $rhs) =>
    let r ← get_monoms lhs
    return (rhs, false) :: r
  | ~q(@HSub.hSub Real Real Real _ $lhs $rhs) =>
    let r ← get_monoms lhs
    return (rhs, true) :: r
  -- Not sure if these two are necessary
  | ~q(@Add.add Real _ $lhs $rhs) =>
    let r ← get_monoms lhs
    return (rhs, false) :: r
  | ~q(@Sub.sub Real _ $lhs $rhs) =>
    let r ← get_monoms lhs
    return (rhs, true) :: r
  | _ =>
    return [(e, false)]

-- Checks if the real number is castable to rat. Castable reals are:
--  · ofNat n
--  · Coe.coe Int Real i
--  · Coe.coe Rat Real i
--  · Div of two castable reals
--  · Neg of castable real
-- I believe this are all the cases that need to be consider after normalizing
-- the expression with `ring_nf` and taking the coefficients
partial def rat_of_real (r: Q(Real)) : MetaM Q(Rat) :=
  match r with
  | ~q(@OfNat.ofNat Real $n $i) => return q(@OfNat.ofNat Rat $n _)
  | ~q(@Coe.coe Nat Real $i $n) => return q(@OfNat.ofNat Rat $n _)
  | ~q(@Coe.coe Int Real $i $n) => return q(@Int.cast Rat _ $n)
  | ~q(@Coe.coe Rat Real $i $n) => return n
  | ~q(@Neg.neg Real $i $n) => do
    let n' ← rat_of_real n
    return q(@Neg.neg Rat _ $n')
  -- TODO: do we need to consider other HDivs?
  | ~q(@HDiv.hDiv Real Real Real $i $e1 $e2) => do
    let e1' ← rat_of_real e1
    let e2' ← rat_of_real e2
    return q(@HDiv.hDiv Rat Rat Rat _ $e1' $e2')
  | _ => throwError "[rat_of_real]: unsupported"

-- given a monomial, compute its coefficient and exponent (as exprs)
partial def get_coeff_exp (monom_neg : Q(Real) × Bool) : MetaM (Q(Rat × Nat)) := do
  let (monom, negated) := monom_neg
  -- TODO: refactor negated branching
  match monom with
  | ~q(@Neg.neg Real _ $e) => get_coeff_exp (e, !negated)
  | ~q(@HMul.hMul Real Real Real _ $lhs $rhs) =>
    let rhs ← rat_of_real rhs
    -- TODO could it be that lhs is an application of neg? I don't think so, but this would break
    match lhs with
    | ~q(@HPow.hPow Real Nat Real _ $base $exp) =>
      if negated then
        return q((-$rhs, $exp))
      else
        return q(($rhs, $exp))
    | _ =>
      if negated then
        return q((-$rhs, 1))
      else
        return q(($rhs, 1))
  | _ =>
    if monom.hasFVar then
      let exp: Q(Nat) ←
        match monom with
        | ~q(@HPow.hPow Real Nat Real _ $base $exp) => return exp
        | _ => return q(1)
      if negated then
        return q((-1, $exp))
      else
        return q((1, $exp))
    else
      let monom ← rat_of_real monom
      if negated then
        return q((-$monom, 0))
      else
        return q(($monom, 0))

def gen_cpoly_array {α : Type*} [Zero α] (coeffs_and_exps : List (α × Nat)) : Raw α :=
  match coeffs_and_exps with
  | [] => #[]
  | (_, exp) :: _ =>
    let arr : Array α := Array.replicate (exp + 1) 0
    go arr coeffs_and_exps
where go arr coeffs_and_exps :=
  match coeffs_and_exps with
  | [] => arr
  | (coeff, exp) :: tl =>
    let arr := arr.set! exp coeff
    go arr tl

def toListExpr (α : Q(Type*)) (es : List Q($α)) : Q(List $α) :=
  match es with
  | [] => q(@List.nil $α)
  | hd :: tl =>
    let tl' : Q(List $α) := toListExpr α tl
    q($hd :: $tl')

def CPolynomial.mk_rat (p : Raw Rat) (pf : p.trim = p) : CPolynomial Rat := ⟨p, pf⟩

def get_comparison (ineq : Q(Prop)) : Expr :=
  match ineq with
  | .app (.app (.app (.app (.const `LT.lt l) i1) i2) _) _ => .app (.app (.const `LT.lt l) i1) i2
  | .app (.app (.app (.app (.const `LE.le l) i1) i2) _) _ => .app (.app (.const `LE.le l) i1) i2
  | .app (.app (.app (.app (.const `GT.gt l) i1) i2) _) _ => .app (.app (.const `GT.gt l) i1) i2
  | .app (.app (.app (.app (.const `GE.ge l) i1) i2) _) _ => .app (.app (.const `GE.ge l) i1) i2
  | .app (.app (.app (.const ``Eq l) i) _) _ => .app (.const ``Eq l) i
  | _ => panic! "[all_to_lhs]: impossible"

partial def get_var (monoms : List (Q(Real) × Bool)) : MetaM (Option Expr) := do
  for (monom, _) in monoms do
    let s ← go monom
    if s.isSome then return s
  return none
where go (m : Q(Real)) : MetaM (Option Expr) :=
  match m with
  | ~q(@Neg.neg _ _ $e) => go e
  | ~q(@HMul.hMul _ _ _ _ $lhs _) => go lhs
  | ~q(@HPow.hPow _ _ _ _ $base _) => go base
  | .fvar _ => return some m
  | _ => return none

def reconsCoveringsUniv (ineq_pfs : Array Expr) (roots_and_polys : Array (Expr × Expr)) : MetaM Unit := do
  for ineq_pf in ineq_pfs do
    -- Transform expressions of the form `¬ (a ≤ b)` in `a > b`
    let ineq_pf ← push_not ineq_pf
    -- Transform expressions of the form `a < b` in `a - b < 0`
    let ineq_pf ← all_to_lhs ineq_pf
    -- Runs `ring_nf` at `ineq_pf`, transforming it into a sum of monomials and joining monomials of same degree
    let ineq_pf ← ring_normalize ineq_pf
    -- Gets the actual expression on the left-hand side of the normalized `ineq_pf`
    let ineq ← inferType ineq_pf
    let lhs := get_lhs ineq
    -- Gets the list of summands (monomial) in `lhs` (with a flag if they come from a subtraction)
    let monoms ← get_monoms lhs
    -- Collects the coefficients and exponents in each monomial (and tries to cast the coefficients to Rat)
    let coeffs_and_exps ← monoms.mapM get_coeff_exp
    -- Create the `CPolynomial.Raw Rat` from the list of coefficients
    let P_raw : Q(Raw Rat) ← mkAppM ``gen_cpoly_array #[toListExpr q(Rat × Nat) coeffs_and_exps]
    -- Proves that `P_raw` is lawful (equal to its `trim`) using `decide +kernel`
    let trim_P_raw : Q(Raw Rat) ← mkAppM ``Raw.trim #[P_raw]
    let P_raw_lawful : Q(Prop) := q($trim_P_raw = $P_raw)
    let P_raw_lawful_pf ← mkDecideProof P_raw_lawful
    -- Create the `CPolynomial Rat` using `P_raw` and the proof that it is lawful
    let P: Q(CPolynomial Rat) ← mkAppM `CPolynomial.mk_rat #[P_raw, P_raw_lawful_pf]
    let cmp: Q(Real -> Real -> Prop) := get_comparison ineq
    let some (var : Q(Real)) ← get_var monoms | throwError "get_var failed"
    let P_eval : Q(Real) := q(CPolynomial.eval₂ (Rat.castHom Real) $var $P)
    let P_comp : Q(Prop) := q($cmp $P_eval 0)
    logInfo m!"P_comp = {P_comp}"
  return ()
