import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign
import Smt.Reconstruct.Real.CAD.LiftIneq
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils

import CompPoly

open Lean Meta Qq CompPoly AlgebraicNumber

/-- `a` is a root of `p` when its defining polynomial divides `p`. The quotient is given as an
explicit witness, `p = a.p * q`, decided on the computable representations, so the kernel only
evaluates a product and an equality (no division). This covers `p = a.p` (`q = 1`) and the usual
case where cvc5's defining polynomial is a factor of the constraint polynomial. -/
lemma isRoot_of_eq_mul (p : CPolynomial Rat) (a : AlgNum) (q : CPolynomial Rat)
    (h : p = a.p * q) : IsRoot p a.toReal := by
  have hdvd : a.p.toPoly ∣ p.toPoly := ⟨q.toPoly, by rw [h, CPolynomial.toPoly_mul]⟩
  have hdvdR : toPolyReal a.p ∣ toPolyReal p := Polynomial.map_dvd ratToRealHom hdvd
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvdR (toReal_root a)

/-- The nonzero coefficients of a native polynomial with their exponents, for `gen_poly`. -/
def coeffsAndExps (p : CPolynomial Rat) : List (Rat × Nat) :=
  (List.range p.size).filterMap fun i =>
    let c := p.coeff i
    if c == 0 then none else some (c, i)

def get_is_root_pf (p : Q(CPolynomial Rat)) (p_native : CPolynomial Rat) (a : RootVal) : Smt.ReconstructM Expr := do
  match a with
  | .rat e q =>
    let e : Q(Rat) := e
    let goal_ev_0 : Q(Prop) := q(CPolynomial.eval $e $p = 0)
    let pf_ev_0 ← mkDecideProof' goal_ev_0
    let pf ← mkAppM ``eval_zero #[e, p, pf_ev_0]
    mkExpectedTypeHint pf q(IsRoot $p (ratToReal $q))
  | .alg e raw =>
    let aE : Q(AlgNum) := e
    let qn := p_native / raw.p
    if decide (raw.p * qn = p_native) then
      trace[smt.reconstruct] "IsRoot: divisibility certificate for {p}"
      let qE : Q(CPolynomial Rat) := gen_poly (coeffsAndExps qn)
      let h ← mkDecideProof' q($p = «$aE».p * $qE)
      return ← mkAppM ``isRoot_of_eq_mul #[p, aE, qE, h]
    let (pf, sign) ← getSignProof p p_native a
    unless sign == 0 do
      throwError "[proveIsRoot]: {e} is not a root of {p} (sign {sign})"
    mkExpectedTypeHint pf q(IsRoot $p (AlgNum.toReal $aE))
