import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils

import CompPoly

open Lean Meta Qq CompPoly AlgebraicNumber

def get_is_root_pf (p : Q(CPolynomial Rat)) (p_native : CPolynomial Rat) (a : RootVal) : Smt.ReconstructM Expr := do
  match a with
  | .rat e q =>
    let e : Q(Rat) := e
    let goal_ev_0 : Q(Prop) := q(CPolynomial.eval $e $p = 0)
    let pf_ev_0 ← mkDecideProof' goal_ev_0
    let pf ← mkAppM ``eval_zero #[e, p, pf_ev_0]
    mkExpectedTypeHint pf q(IsRoot $p (ratToReal $q))
-- NOTE: we know a is a root of a.p already
-- TODO 1: If a.p = p we can just use Sturm
-- TODO 2: If a.p | p then p = a.p * k; proving a is root of a.p is enough to conclude it is root of p
-- TODO 3: Otherwise we can do some gcd trick, but then it is not clear that it is less expensive than
-- getSignProof.
  | .alg e _ =>
    let (pf, sign) ← getSignProof p p_native a
    unless sign == 0 do
      throwError "[proveIsRoot]: {e} is not a root of {p} (sign {sign})"
    let a : Q(AlgNum) := e
    mkExpectedTypeHint pf q(IsRoot $p (AlgNum.toReal $a))
