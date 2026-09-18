import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.NormalizePoly
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign

import CompPoly

open Lean Qq CompPoly

#check SgnInv

variable (p : CPolynomial Rat)
variable (x y : Real)
variable (S : Set Real)
variable (hx : x ∈ S)
variable (hy : y ∈ S)

variable (hs : SgnInv p S)

#check hs x hx y hy

def sgnInvElimCore (var : Q(Real)) (P : Q(CPolynomial Rat)) (P_native : CPolynomial Rat) (sample : RootVal) (lb ub : Option RootVal)
    (h_sgn_inv : Expr) (h_P_constr : Expr) : Smt.ReconstructM Expr := do
  let ineqPf ← liftConstraint P var h_P_constr
  let ⟨pf_sample_sign, sign⟩  ← getSignProof P P_native sample
  match lb, ub with
  | none, none => logInfo "foo"
  | some lb, none => sorry
  | none, some ub => sorry
  | some lb, some ub =>
    let lb_sample ← gen_toReal_lt lb sample
    let sample_ub ← gen_toReal_lt sample ub
    let lb_real : Q(Real) ← lb.toReal
    let ub_real : Q(Real) ← ub.toReal
    let S : Q(Set Real) := q(Set.Ioo $lb_real $ub_real)
    let sampleR : Q(Real) ← sample.toReal
    let sampleInS : Expr := q($sampleR ∈ $S)
    let sampleInSMv ← Meta.mkFreshExprMVar sampleInS
    let memPf ← Meta.mkAppM ``And.intro #[lb_sample, sample_ub]
    let memPf ← Meta.mkExpectedTypeHint memPf sampleInS
    let goal := q(¬ $var ∈ $S)
    let goalMVar ← Meta.mkFreshExprMVar goal
    let (h, mvFalse) ← goalMVar.mvarId!.intro1P
    mvFalse.withContext do
      let same_sign := Meta.mkAppM' h_sgn_inv #[var, .fvar h, sampleR, memPf]
      sorry
  sorry
