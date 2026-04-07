import Lean

import Smt.Reconstruct.Real.CAD.Sturm.Decidable
import Smt.Reconstruct.Real.CAD.Utils

open Qq Lean Elab Tactic ToExpr Meta
open CompPoly
open Theorem

lemma der_toPoly_toReal (P : CPolynomial Rat) :
    P.derivative.toPoly.map (Rat.castHom Real) = (P.toPoly.map (Rat.castHom Real)).derivative := by
  rw [CPolynomial.derivative_toPoly, Polynomial.derivative_map]

instance : ToString (CPolynomial.Raw Rat) where
  toString p := toString (p : Array Rat)

instance : ToString (CPolynomial Rat) where
  toString p := toString p.val

lemma cast_int_eq {a b : Nat} : (a : Int) = (b : Int) → a = b := by
  intro h
  exact Int.ofNat_inj.mp h

def gen_root_counting_proof (p : Q(CPolynomial ℚ)) : MetaM Expr := do
  let p_der : Q(CPolynomial ℚ) ← mkAppM ``CPolynomial.derivative #[p]
  let seqVar ← mkAppM ``seqVarLineSturmC' #[p, p_der]
  let seqVarVal : Int ← unsafe Meta.evalExpr Int (q(Int)) seqVar
  let cpoly_seq : Q(Prop) := q(seqVarLineSturmC' $p $p_der = $seqVarVal)
  let cpoly_seq_pf ← mkDecideProof cpoly_seq
  let cpoly_poly ← mkAppM ``seqVarLineEquivSturm' #[p, p_der]
  let poly_roots_pf ← mkAppM ``Eq.trans #[cpoly_poly, cpoly_seq_pf]
  let poly_roots_pf' ← rewriteWithEq poly_roots_pf (← mkAppM ``der_toPoly_toReal #[p])
  let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
  let sturm_R_p ← mkAppM ``sturm_R #[p_real]
  let intPf : Q((2 : Int) = 3) ← mkAppM ``Eq.trans #[sturm_R_p, poly_roots_pf']
  mkAppM ``cast_int_eq #[intPf]

syntax (name := count_roots) "count_roots" term : tactic

@[tactic count_roots] def evalCountRoots : Tactic := fun stx => withMainContext do
  let p : Q(CPolynomial ℚ) ← elabTerm stx[1] none
  let p_roots_pf ← gen_root_counting_proof p
  closeMainGoal (.anonymous) p_roots_pf

section Tests

open CPolynomial

def P : CPolynomial ℚ := X ^ 4 + X ^ 3 - X - 1

lemma P_roots : (toPolyReal P).roots.toFinset.card = 2 := by count_roots P

#print axioms P_roots

def Q : CPolynomial ℚ := X ^ 2 + 1

lemma Q_roots : (toPolyReal Q).roots.toFinset.card = 0 := by count_roots Q

#print axioms Q_roots

end Tests
