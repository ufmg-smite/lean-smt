import Lean

import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.Sturm.Decidable
import Smt.Reconstruct.Real.CAD.Sturm.Certificate
import Smt.Reconstruct.Real.CAD.Utils

open Qq Lean Elab Tactic ToExpr Meta
open CompPoly
open Theorem

instance : ToString (CPolynomial.Raw Rat) where
  toString p := toString (p : Array Rat)

instance : ToString (CPolynomial Rat) where
  toString p := toString p.val

lemma cast_int_eq {a b : Nat} : (a : Int) = (b : Int) → a = b := by
  intro h
  exact Int.ofNat_inj.mp h

/-- Proves `(toPolyReal p).roots.toFinset.card = n`. With `cert? = some (h, S)`, where
`h : SturmCert.certOk p p.derivative … = true` certifies the sequence `S`, the sign variations are
counted on `S` instead of a Sturm sequence computed in the kernel. -/
def gen_root_counting_proof (p : Q(CPolynomial ℚ)) (p_native : CPolynomial Rat)
    (cert? : Option (Expr × Expr) := none) : Smt.ReconstructM Expr := do
  let p_der : Q(CPolynomial ℚ) ← mkAppM ``CPolynomial.derivative #[p]
  let p_native_der := p_native.derivative
  let seqVar_native : Int := seqVarLineSturmC' p_native p_native_der
  let n : Q(ℤ) := q($seqVar_native)
  let cpoly_seq_pf ← match cert? with
    | none => mkDecideProof' q(seqVarLineSturmC' $p $p_der = $n)
    | some (hcert, seq) => do
      let hcount ← mkDecideProof' (← mkEq (← mkAppM ``seqVarLineC' #[seq]) n)
      mkEqTrans (← mkAppM ``SturmCert.seqVarLineSturmC'_eq_of_certOk #[hcert]) hcount
  let cpoly_poly ← mkAppM ``seqVarLineEquivSturm' #[p, p_der]
  let poly_roots_pf ← mkAppM ``Eq.trans #[cpoly_poly, cpoly_seq_pf]
  let poly_roots_pf' ← rewriteWithEq poly_roots_pf (← mkAppM ``der_toPoly_toReal #[p])
  let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
  let sturm_R_p ← mkAppM ``sturm_R #[p_real]
  let intPf ← mkAppM ``Eq.trans #[sturm_R_p, poly_roots_pf']
  mkAppM ``cast_int_eq #[intPf]

syntax (name := count_roots) "count_roots" term : tactic

@[tactic count_roots] def evalCountRoots : Tactic := fun stx => withMainContext do
  let p : Q(CPolynomial ℚ) ← elabTerm stx[1] none
  let p_native ← unsafe evalExpr (CPolynomial Rat) q(CPolynomial Rat) p
  let p_roots_pf ← ((gen_root_counting_proof p p_native).run {}).run' {}
  closeMainGoal (.anonymous) p_roots_pf

section Tests

open CPolynomial

def P : CPolynomial ℚ := X ^ 4 + X ^ 3 - X - 1

lemma P_roots : (toPolyReal P).roots.toFinset.card = 2 := by count_roots P

def Q : CPolynomial ℚ := X ^ 2 + 1

lemma Q_roots : (toPolyReal Q).roots.toFinset.card = 0 := by count_roots Q

end Tests
