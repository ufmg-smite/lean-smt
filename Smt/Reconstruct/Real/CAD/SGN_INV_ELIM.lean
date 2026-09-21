import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.NormalizePoly
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign

import CompPoly

open Lean Qq Meta CompPoly

/-- Turns a constraint `e ~ 0` (in the canonical shape produced by `liftConstraint`) into the
corresponding statement about `SignType.sign e`:

  `e < 0` ↦ `sign e = -1`   `e > 0` ↦ `sign e = 1`    `e = 0` ↦ `sign e = 0`
  `e ≤ 0` ↦ `sign e ≤ 0`    `e ≥ 0` ↦ `0 ≤ sign e`    `¬ e = 0` ↦ `sign e ≠ 0` -/
def constrToSign (pf : Expr) : MetaM Expr := do
  let t ← instantiateMVars (← inferType pf)
  match t with
  | .app (.app (.app (.app (.const ``LT.lt _) _) _) e') _ =>
    have e : Q(Real) := e'
    have pf : Q($e < 0) := pf
    return q(sign_eq_neg_one_iff.mpr $pf)
  | .app (.app (.app (.app (.const ``GT.gt _) _) _) e') _ =>
    have e : Q(Real) := e'
    have pf : Q(0 < $e) := pf
    return q(sign_eq_one_iff.mpr $pf)
  | .app (.app (.app (.app (.const ``LE.le _) _) _) e') _ =>
    have e : Q(Real) := e'
    have pf : Q($e ≤ 0) := pf
    return q(sign_nonpos_iff.mpr $pf)
  | .app (.app (.app (.app (.const ``GE.ge _) _) _) e') _ =>
    have e : Q(Real) := e'
    have pf : Q(0 ≤ $e) := pf
    return q(sign_nonneg_iff.mpr $pf)
  | .app (.app (.app (.const ``Eq _) _) e') _ =>
    have e : Q(Real) := e'
    have pf : Q($e = 0) := pf
    return q(sign_eq_zero_iff.mpr $pf)
  | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) _) e') _) =>
    have e : Q(Real) := e'
    have pf : Q($e ≠ 0) := pf
    return q(sign_ne_zero.mpr $pf)
  | _ => throwError "[constrToSign]: unsupported constraint {t}"

def sgnInvElimCore (var : Q(Real)) (P : Q(CPolynomial Rat)) (P_native : CPolynomial Rat) (sample : RootVal) (lb ub : Option RootVal)
    (h_sgn_inv : Expr) (h_P_constr : Expr) : Smt.ReconstructM Expr := do
  let ineq_pf ← liftConstraint P var h_P_constr
  let sampleR : Q(Real) ← sample.toReal
  let ⟨pf_sample_sign, _⟩  ← getSignProof P P_native sample
  let (S, mem_pf) ← match lb, ub with
  | none, none =>
    let S : Q(Set Real) := q(Set.univ : Set Real)
    let mem := q($sampleR ∈ $S)
    let mem_pf ← mkExpectedTypeHint (← mkAppM ``Set.mem_univ #[sampleR]) mem
    pure (S, mem_pf)
  | some lb, none =>
    let lb_sample ← gen_toReal_lt lb sample
    let lb_real : Q(Real) ← lb.toReal
    let S : Q(Set Real) := q(Set.Ioi $lb_real)
    let mem := q($sampleR ∈ $S)
    let mem_pf ← mkExpectedTypeHint lb_sample mem
    pure (S, mem_pf)
  | none, some ub =>
    let sample_ub ← gen_toReal_lt sample ub
    let ub_real : Q(Real) ← ub.toReal
    let S : Q(Set Real) := q(Set.Iio $ub_real)
    let mem := q($sampleR ∈ $S)
    let mem_pf ← mkExpectedTypeHint sample_ub mem
    pure (S, mem_pf)
  | some lb, some ub =>
    let lb_sample ← gen_toReal_lt lb sample
    let sample_ub ← gen_toReal_lt sample ub
    let lb_real : Q(Real) ← lb.toReal
    let ub_real : Q(Real) ← ub.toReal
    let S : Q(Set Real) := q(Set.Ioo $lb_real $ub_real)
    let mem := q($sampleR ∈ $S)
    let mem_pf ← mkAppM ``And.intro #[lb_sample, sample_ub]
    let mem_pf ← mkExpectedTypeHint mem_pf mem
    pure (S, mem_pf)
  let goal := q(¬ $var ∈ $S)
  let notMemPf ← mkFreshExprMVar goal
  let (h, mvFalse) ← notMemPf.mvarId!.intro1P
  mvFalse.withContext do
    let same_sign ← mkAppM' h_sgn_inv #[var, .fvar h, sampleR, mem_pf]
    let sign_x ← constrToSign ineq_pf
    let sign_s ← constrToSign pf_sample_sign
    let closed ← rewriteWithEq sign_x same_sign
    let closed ← rewriteWithEq closed sign_s
    let t ← inferType closed
    let refutation ← mkDecideProof (mkNot t)
    mvFalse.assign (← mkAppOptM ``absurd #[t, q(False), closed, refutation])
  let notMemPf ← instantiateMVars notMemPf
  match lb, ub with
  | none, none => pure (mkApp notMemPf q(Set.mem_univ $var))
  | _, _ => return notMemPf

namespace sgn_inv_elim_tests

open Elab Tactic

--                                               var      l                        r              sample   sgn_inv pf  literal pf
syntax (name := sgn_inv_elim_tac) "sgn_inv_elim" term "," "[" (term)? "]" "," "[" (term)? "]" "," term "," term ","    term : tactic

@[tactic sgn_inv_elim_tac] def evalSgnInvElim : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| sgn_inv_elim $vStx , [ $[$lbStx]? ], [ $[$ubStx]? ], $sStx, $h1Stx, $h2Stx ) =>
    let var ← elabTerm vStx none
    let lb ← lbStx.mapM fun t => do RootVal.ofExpr (← elabTerm t none)
    let ub ← ubStx.mapM fun t => do RootVal.ofExpr (← elabTerm t none)
    let sample ← elabTerm sStx none
    let sample_native ← RootVal.ofExpr sample
    let h_sgn_inv ← elabTerm h1Stx none
    let ineq_pf ← elabTerm h2Stx none
    let sgn_inv_T ← inferType h_sgn_inv
    let P : Q(CPolynomial Rat) := sgn_inv_T.getArg! 0
    let P_native ← unsafe evalExpr (CPolynomial Rat) (q(CPolynomial Rat)) P
    let pf ← ((sgnInvElimCore var P P_native sample_native lb ub h_sgn_inv ineq_pf).run {}).run' {}
    closeMainGoal .anonymous pf
  | _ => throwError "unexpected syntax"

-- p = x - 5 is negative at the sample 2, so `p(a) > 0` excludes `a` from (1, 3)
example (a : Real)
    (hS : SgnInv (CPolynomial.C (-5) + CPolynomial.C 1 * CPolynomial.X) (Set.Ioo (ratToReal 1) (ratToReal 3)))
    (hC : (-5) + 1 * a > 0) : ¬ (a > ratToReal 1 ∧ a < ratToReal 3) := by
  sgn_inv_elim a, [ (1 : Rat) ], [(3 : Rat)], (2 : Rat), hS, hC

-- non-strict constraint, given negated, on a half-line: `¬ (p(a) < 0)` is `p(a) ≥ 0`
example (a : Real)
    (hS : SgnInv (CPolynomial.C (-5) + CPolynomial.C 1 * CPolynomial.X) (Set.Iio (ratToReal 4)))
    (hC : ¬ ((-5) + 1 * a < 0)) : ¬ (a < ratToReal 4) := by
  sgn_inv_elim a, [], [(4 : Rat)], (2 : Rat), hS, hC

-- p = x² - 4 has a root at the sample 2: a disequality excludes the right half-line from it
example (a : Real)
    (hS : SgnInv (CPolynomial.C (-4) + CPolynomial.C 1 * CPolynomial.X ^ 2) (Set.Ioi (ratToReal 1)))
    (hC : ¬ ((-4) + 1 * a * a = 0)) : ¬ (a > ratToReal 1) := by
  sgn_inv_elim a, [(1 : Rat)], [], (2 : Rat), hS, hC

-- whole line: the conclusion is `False`
example (a : Real)
    (hS : SgnInv (CPolynomial.C 3) Set.univ)
    (hC : (3 : Real) ≤ 0) : False := by
  sgn_inv_elim a, [], [], (0 : Rat), hS, hC

-- algebraic lower bound: the root of 10x² + 2x - 15 isolated in (1, 5/4)
def pA : CPolynomial Rat := CPolynomial.C (-15) + CPolynomial.C 2 * CPolynomial.X + CPolynomial.C 10 * CPolynomial.X ^ 2
def rA : AlgebraicNumber.Raw := ⟨pA, 1, 5/4⟩
def aA : AlgebraicNumber.AlgNum := by lift_alg_num rA

example (a : Real)
    (hS : SgnInv (CPolynomial.C (-15) + CPolynomial.C 2 * CPolynomial.X + CPolynomial.C 10 * CPolynomial.X ^ 2) (Set.Ioi aA.toReal))
    (hC : (-15) + 2 * a + 10 * a * a = 0) : ¬ (a > aA.toReal) := by
  sgn_inv_elim a, [aA], [], (2 : Rat), hS, hC

end sgn_inv_elim_tests
