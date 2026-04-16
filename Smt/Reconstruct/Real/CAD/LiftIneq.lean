import Lean
import Lean.Meta.Tactic.Simp

import Smt.Reconstruct.Real.CAD.NormalizePoly
import Smt.Reconstruct.Real.CAD.CountRoots
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign

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
-- I believe these are all the cases that need to be consider after normalizing
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

def natOfExpr (e: Q(Nat)) : MetaM Nat := do
  match e.rawNatLit? with
  | none =>
    match e with
    | ~q(@OfNat.ofNat _ $n _) => return n.rawNatLit?.get!
    | _ => panic! "natOfExpr"
  | some n => return n

partial def get_coeff_exp (monom_neg : Q(Real) × Bool) : MetaM (Q(Rat) × Nat) := do
  let (monom, negated) := monom_neg
  -- TODO: refactor negated branching
  match monom with
  | ~q(@Neg.neg Real _ $e) => get_coeff_exp (e, !negated)
  | ~q(@HMul.hMul Real Real Real _ $lhs $rhs) =>
    let rhs ← rat_of_real rhs
    -- TODO could it be that lhs is an application of neg? I don't think so, but this would break
    match lhs with
    | ~q(@HPow.hPow Real Nat Real _ $base $exp) =>
      if negated then return (q(-$rhs), ← natOfExpr exp)
      else return (q($rhs), ← natOfExpr exp)
    | _ =>
      if negated then return (q(-$rhs), 1)
      else return (q($rhs), 1)
  | _ =>
    if monom.hasFVar then
      let exp: Q(Nat) ←
        match monom with
        | ~q(@HPow.hPow Real Nat Real _ $base $exp) => return exp
        | _ => return q(1)
      if negated then return (q(-1), ← natOfExpr exp)
      else return (q(1), ← natOfExpr exp)
    else
      let monom ← rat_of_real monom
      if negated then return (q(-$monom), 0)
      else return (q($monom), 0)

-- sligthly different from toListExpr, but can't be implemented as a specialization of that
def toListExpr' (es : List (Q(Rat) × Nat)) : Q(List (Rat × Nat)) :=
  match es with
  | [] => q(@List.nil (Rat × Nat))
  | (r, n) :: tl =>
    let tl' : Q(List (Rat × Nat)) := toListExpr' tl
    let hd := q(($r, $n))
    q($hd :: $tl')

def CPolynomial.mk_rat (p : Raw Rat) (pf : p.trim = p) : CPolynomial Rat := ⟨p, pf⟩

def get_comparison (ineq : Q(Prop)) : Expr :=
  match ineq with
  | .app (.app (.app (.app (.const `LT.lt l) i1) i2) _) _ => .app (.app (.const `LT.lt l) i1) i2
  | .app (.app (.app (.app (.const `LE.le l) i1) i2) _) _ => .app (.app (.const `LE.le l) i1) i2
  | .app (.app (.app (.app (.const `GT.gt l) i1) i2) _) _ => .app (.app (.const `GT.gt l) i1) i2
  | .app (.app (.app (.app (.const `GE.ge l) i1) i2) _) _ => .app (.app (.const `GE.ge l) i1) i2
  | .app (.app (.app (.const ``Eq l) i) _) _ => .app (.const ``Eq l) i
  | _ => panic! "[get_comparison]: impossible"

@[simp, grind =]
private def zero_rat : Rat := 0

def gen_poly (coeffs_and_exps : List (Q(Rat) × Nat)) : Q(CPolynomial Rat) :=
  match coeffs_and_exps with
  | [] => q(C 0)
  | [(c, e)] =>
    if e == 0 then
      q(CPolynomial.C $c)
    else if e == 1 then
      q((CPolynomial.C $c) * (X : CPolynomial Rat))
    else
      q((CPolynomial.C $c) * ((X : CPolynomial Rat) ^ $e))
  | (c, e) :: tl =>
    let p' : Q(CPolynomial Rat) := gen_poly tl
    if e == 0 then
      q(CPolynomial.C $c + $p')
    else if e == 1 then
      q((CPolynomial.C $c) * (X : CPolynomial Rat) + $p')
    else
      q((CPolynomial.C $c) * ((X : CPolynomial Rat) ^ $e) + $p')

-- retrieves a polynomial and a proof of inequality involving it,
-- given a proof of an inequality involving a free variable
def lift_ineq (ineq_pf : Expr) (var : Q(Real)) : MetaM (Expr × Expr) := do
  let t1 ← IO.monoMsNow
  -- Transform expressions of the form `¬ (a ≤ b)` in `a > b`
  let ineq_pf ← push_not ineq_pf
  let t2 ← IO.monoMsNow
  logInfo m!"push neg took {t2 - t1}ms"
  -- Transform expressions of the form `a < b` in `a - b < 0`
  let ineq_pf ← all_to_lhs ineq_pf
  let t3 ← IO.monoMsNow
  logInfo m!"all_to_lhs took {t3 - t2}ms"
  -- Runs `ring_nf` at `ineq_pf`, transforming it into a sum of monomials and joining monomials of same degree
  let ineq_pf ← ring_normalize ineq_pf
  let t4 ← IO.monoMsNow
  logInfo m!"ring normalize took {t4 - t3}ms"
  -- Gets the expression on the left-hand side of the normalized `ineq_pf`
  let ineq ← inferType ineq_pf
  let lhs: Q(Real) := get_lhs ineq
  -- Gets the list of summands (monomial) in `lhs` (with a flag if they come from a subtraction)
  let monoms ← get_monoms lhs
  let t5 ← IO.monoMsNow
  logInfo m!"get_monoms took {t5 - t4}ms"
  -- Collects the coefficients and exponents in each monomial (and tries to cast the coefficients to Rat)
  let coeffs_and_exps ← monoms.mapM get_coeff_exp
  let t6 ← IO.monoMsNow
  logInfo m!"coeffs and exps took {t6 - t5}ms"

  let P := gen_poly coeffs_and_exps
  let P_eval : Q(Real) := q((toPolyReal $P).eval $var)
  let P_eval_eq : Q(Prop) := q($P_eval = $lhs)
  let P_eval_eq_pf ← mkFreshExprMVar P_eval_eq
  let remaining_goal? ← simp' P_eval_eq_pf.mvarId!
    (List.map mkConst [``toPolyReal.eq_1, ``ratToRealHom.eq_1, ``toPoly_add, ``toPoly_sub, ``toPoly_mul, ``toPoly_pow, ``C_toPoly, ``X_toPoly])
  match remaining_goal? with
  | some mv =>
    let ok ← runGrind mv
    if !ok then throwError "grind failed 7"
  | none => pure ()
  let t7 ← IO.monoMsNow
  logInfo m!"eval = lhs took {t7 - t6}ms"
  let cmp: Q(Real -> Real -> Prop) := get_comparison ineq
  let P_comp : Q(Prop) := q($cmp $P_eval 0)
  let P_comp_mv ← mkFreshExprMVar P_comp
  let P_comp_pf ← rewriteMVar P_comp_mv.mvarId! P_eval_eq_pf
  P_comp_pf.assign ineq_pf

  return (P, P_comp_mv)

open AlgebraicNumber

syntax (name := lift_ineq_tac) "lift_ineq" term "," term : tactic

@[tactic lift_ineq_tac] def evalLiftIneqTac : Tactic := fun stx => withMainContext do
  let e ← elabTerm stx[1] none
  let var ← elabTerm stx[3] none
  let g ← getMainGoal
  let (P, ineq_pf) ← lift_ineq e var
  closeMainGoal .anonymous ineq_pf

namespace tests_lift_ineq

def p : CPolynomial Rat := -3/2 + X

example (a : Real) (h : ¬ -1 * a ≥ -3 / 2) : Polynomial.eval a (toPolyReal p) > 0 := by
  lift_ineq h , a

end tests_lift_ineq
