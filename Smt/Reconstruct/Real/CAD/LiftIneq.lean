import Lean
import Lean.Meta.Tactic.Simp

import Smt.Reconstruct.Real.CAD.CPolynomial
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

def gen_cpoly_array {α : Type*} (zero : α) (coeffs_and_exps : List (α × Nat)) : Array α :=
  match coeffs_and_exps with
  | [] => #[]
  | (_, exp) :: _ =>
    let arr : Array α := Array.replicate (exp + 1) zero
    go arr coeffs_and_exps
where go arr coeffs_and_exps :=
  match coeffs_and_exps with
  | [] => arr
  | (coeff, exp) :: tl =>
    let arr := arr.set! exp coeff
    go arr tl

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
  | [(c, e)] => q(C $c • ((X : CPolynomial Rat) ^ $e))
  | (c, e) :: tl =>
    let p' : Q(CPolynomial Rat) := gen_poly tl
    q(C $c • ((X : CPolynomial Rat) ^ $e) + $p')

-- given a proof that some expression of the form `f(var) <> 0` is true, produce a proof
-- that `P.eval var <> 0`, where `P` is the polynomial corresponding to `f`. See `p_comp_pf_ex`.
def prove_p_comp (var : Q(Real)) (P: Q(CPolynomial Rat)) (coeffs_and_exps : List (Q(Rat) × Nat)) (ineq_pf : Expr) (P_comp : Expr) : MetaM Expr := do
  let (_, deg_nat) :: _ ← pure coeffs_and_exps | throwError "[prove_p_comp] impossible 1"
  let t1 ← IO.monoMsNow
  let p_deg : Q(Prop) := q(CPolynomial.natDegree $P = $deg_nat)
  let p_deg_pf : Q($p_deg) ← mkDecideProof p_deg
  let t2 ← IO.monoMsNow
  logInfo m!"degree proof took {t2 - t1}ms"

  let finset_range_lhs : Q(Finset Nat) := q(Finset.range ($deg_nat + 1))
  let finset_range_rhs : Q(Finset Nat) := go deg_nat
  let finset_range_prop : Q(Prop) ← mkAppM `Eq #[finset_range_lhs, finset_range_rhs]
  let finset_range_pf ← mkDecideProof finset_range_prop
  let t3 ← IO.monoMsNow
  logInfo m!"finset identity took {t3 - t2}ms"

  let mv_e ← mkFreshExprMVar P_comp
  let mut mv := mv_e.mvarId!
  let g := mv
  mv ← rewriteMVar mv q(CPolynomial.eval_toPolyReal_eq_sum_range $P $var)
  mv ← rewriteMVar mv p_deg_pf
  mv ← rewriteMVar mv finset_range_pf
  let t4 ← IO.monoMsNow
  logInfo m!"rewriting mv took {t4 - t3}ms"

  let curr_goal ← mv.getType
  let lhs := get_lhs curr_goal
  let rhs := gen_sum deg_nat var
  let expand_sum_prop ← mkAppM `Eq #[lhs, rhs]
  logInfo m!"expand sum prop = {expand_sum_prop}"
  let expand_sum_mv ← mkFreshExprMVar expand_sum_prop
  normNum expand_sum_mv.mvarId!

  let t5 ← IO.monoMsNow
  logInfo m!"expand sum proof took {t5 - t4}ms"

  mv ← rewriteMVar mv expand_sum_mv

  let mut curr: Q(Nat) := q(0)
  let mut coeffs_and_exps_arr := gen_cpoly_array q(0 : Rat) coeffs_and_exps
  for i in List.range (deg_nat + 1) do
    let coeff_i ← mkAppM ``CPolynomial.coeff #[P, curr]
    let val := coeffs_and_exps_arr.getD i (mkConst ``zero_rat)
    let eq_p ← mkAppM `Eq #[coeff_i, val]
    let eq_p_pf ← mkDecideProof eq_p
    mv ← rewriteMVar mv eq_p_pf
    curr := q($curr + 1)

  let t6 ← IO.monoMsNow
  logInfo m!"rewriting coefficients took {t6 - t5}ms"

  -- I don't understand why we need `ineq_pf` here but it doesn't work without it
  let mv? ← simp' mv [ineq_pf]
  match mv? with
  | none => pure ()
  | some mv' =>
    let ok ← runGrind mv'
    if !ok then
      throwError "grind failed 7"

  let t7 ← IO.monoMsNow
  logInfo m!"last step took {t7 - t6}ms"

  let e ← getExprMVarAssignment? g
  return e.get!
where
  go (curr : Nat) : Q(Finset Nat) :=
    match curr with
    | 0 => q(singleton 0)
    | curr + 1 =>
      let r := go curr
      q(insert ($curr + 1) $r)
  gen_sum (d: Nat) (var : Q(Real)) : Q(Real) :=
    match d with
    | 0 => q(ratToRealHom (CPolynomial.coeff $P 0) * ($var ^ 0))
    | d + 1 =>
      let r: Q(Real) := gen_sum d var
      let curr := q(ratToRealHom (CPolynomial.coeff $P ($d + 1)))
      let curr := q($curr * ($var ^ ($d + 1)))
      q($curr + $r)

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
  let lhs := get_lhs ineq
  -- Gets the list of summands (monomial) in `lhs` (with a flag if they come from a subtraction)
  let monoms ← get_monoms lhs
  let t5 ← IO.monoMsNow
  logInfo m!"get_monoms took {t5 - t4}ms"
  -- Collects the coefficients and exponents in each monomial (and tries to cast the coefficients to Rat)
  let coeffs_and_exps ← monoms.mapM get_coeff_exp
  let t6 ← IO.monoMsNow
  logInfo m!"get coeff exp took {t6 - t5}ms"
  -- Create the `CPolynomial.Raw Rat` from the list of coefficients
  let P_raw : Q(Raw Rat) ← mkAppM ``gen_cpoly_array #[q(0: Rat), toListExpr' coeffs_and_exps]
  let trim_P_raw : Q(Raw Rat) ← mkAppM ``Raw.trim #[P_raw]
  let P_raw_lawful : Q(Prop) := q($trim_P_raw = $P_raw)
  let P_raw_lawful_pf ← mkDecideProof P_raw_lawful
  let t7 ← IO.monoMsNow
  logInfo m!"lawful proof took {t7 - t6}ms"
  -- Create the `CPolynomial Rat` using `P_raw` and the proof that it is lawful
  let P: Q(CPolynomial Rat) ← mkAppM `CPolynomial.mk_rat #[P_raw, P_raw_lawful_pf]
  let cmp: Q(Real -> Real -> Prop) := get_comparison ineq
  let P_eval : Q(Real) := q((toPolyReal $P).eval $var)
  let P_comp : Q(Prop) := q($cmp $P_eval 0)
  -- Proves that P(var) <> 0, according to the original `ineq_pf`
  let P_comp_pf ← prove_p_comp var P coeffs_and_exps ineq_pf P_comp
  let t8 ← IO.monoMsNow
  logInfo m!"prove comparison took {t8 - t7}ms"
  return (P, P_comp_pf)

open AlgebraicNumber

syntax (name := lift_ineq_tac) "lift_ineq" term "," term : tactic

@[tactic lift_ineq_tac] def evalLiftIneqTac : Tactic := fun stx => withMainContext do
  let e ← elabTerm stx[1] none
  let var ← elabTerm stx[3] none
  let g ← getMainGoal
  let (P, ineq_pf) ← lift_ineq e var
  closeMainGoal .anonymous ineq_pf

namespace tests_lift_ineq

def p : CPolynomial Rat := CPolynomial.mk_rat (gen_cpoly_array 0 [(1, 1), (-3 / 2, 0)]) (by decide +kernel)

example (a : Real) (h : ¬ -1 * a ≥ -3 / 2) : Polynomial.eval a (toPolyReal p) > 0 := by
  lift_ineq h , a

