import Lean
import Lean.Meta.Tactic.Simp

import Smt.Reconstruct.Real.CAD.CountRoots
import Smt.Reconstruct.Real.CAD.CPolynomial
import Smt.Reconstruct.Real.CAD.LiftIneq
import Smt.Reconstruct.Real.CAD.NormalizePoly
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign

open Qq Lean Elab Tactic Meta

open CompPoly
open CPolynomial

open AlgebraicNumber

--                                   inequality proofs  roots
syntax (name := univ_cad) "univ_cad" ("[" term,* "]")   ("[" term,* "]") : tactic

def parseUnivCad : Syntax → TacticM (List Expr × List Q(AlgNum))
  | `(tactic| univ_cad [ $[$as],* ] [ $[$bs],* ] ) => do
    let as' ← as.toList.mapM (elabTerm · none)
    let bs' ← bs.toList.mapM (elabTerm · none)
    return (as', bs')
  | _ => throwError "[parseUnivCad]: impossible"

def gen_root_counting_proof' (p : Q(CPolynomial Rat)) : MetaM Expr := do
  let pf ← gen_root_counting_proof p
  let s : Q(Finset Real) := q((toPolyReal $p).roots.toFinset)
  let eq_pf := q(Eq.symm (Finset.length_sort (α := Real) (s := $s) (· ≤ ·)))
  rewriteWithEq pf eq_pf

def computeSortedRootSet (p : Q(CPolynomial Rat)) (rs : List Q(AlgNum)) (roots_card rs_sorted : Expr) (roots_pfs : List Expr) : MetaM Expr := do
  let rs_real : List Q(Real) := rs.map (fun qa: Q(AlgNum) => q(AlgNum.toReal $qa))
  let rs_real' : Q(List Real) := toListExpr q(Real) rs_real

  let p_ne_0_goal : Q(Prop) := q($p ≠ 0)
  let p_ne_0 ← mkDecideProof p_ne_0_goal
  let p_polyReal_ne_0' ← mkAppM ``toPolyReal_zero #[p, p_ne_0]
  let p_ne_0 ← mkAppM ``gneg_imp_gtopoly_neg #[p, p_ne_0]

  let toPolyReal_rev ← mkAppM ``toPolyReal.eq_1 #[p]

  let hyp1 : Q(Prop) := q(List.length $rs_real' = (toPolyReal $p).roots.toFinset.sort.length)
  let mv1 ← mkFreshExprMVar hyp1
  let hyp1_pf : Q($hyp1) := mv1
  let mv1' ← simp' mv1.mvarId! []
  let mv1' ← rewriteMVar mv1' roots_card
  mv1'.refl

  let hyp2 : Q(Prop) := q(∀ i ∈ $rs_real', i ∈ (toPolyReal $p).roots.toFinset.sort (· ≤ ·))
  let mv2 ← mkFreshExprMVar hyp2
  let hyp2_pf := mv2
  let mv2' ← simp' mv2.mvarId! (p_ne_0 :: roots_pfs)
  mv2'.assign p_polyReal_ne_0'

  let hyp3_pf := rs_sorted
  let hyp4_pf := q(Finset.sortedLT_sort (toPolyReal $p).roots.toFinset)
  mkAppM ``list_eq_of_sorted_of_length_of_mem #[rs_real', q((toPolyReal $p).roots.toFinset.sort (· ≤ ·)), hyp1_pf, hyp2_pf, hyp3_pf, hyp4_pf]

@[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do
  let (ineq_pfs, rs) ← parseUnivCad stx
  let ineq_pf := ineq_pfs[0]!
  let (P, sgn_P_pf) ← lift_ineq ineq_pf
  let P_n_roots ← gen_root_counting_proof P
  let r0_root ← getSignProof P rs[0]!
  let r1_root ← getSignProof P rs[1]!
  let rs_sorted ← genPfSortedLT rs
  let e ← computeSortedRootSet P rs P_n_roots rs_sorted [r0_root, r1_root]
  closeMainGoal .anonymous e

def r3 : Rat := 3 / 2

open CPolynomial in
def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15

def r1 : Raw := ⟨p1, -3/2, -5/4⟩
def R1 : AlgNum := by lift_alg_num r1

def r2 : Raw := ⟨p1, 1, 5/4⟩
def R2 : AlgNum := by lift_alg_num r2

example (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : [R1.toReal, R2.toReal] = (toPolyReal (mk_rat (gen_cpoly_array 0 [(5, 2), (1, 1), (-15 / 2, 0)]) (by decide +kernel))).roots.toFinset.sort := by
  univ_cad [h2] [R1, R2]

namespace main_tests

syntax (name := compute_root_set) "compute_root_set" term "," ("[" term,* "]") : tactic
def parseComputeRootSet : Syntax → TacticM (Q(CPolynomial Rat) × List Q(AlgNum))
  | `(tactic| compute_root_set $p , [ $[$rs],* ] ) => do
    let rs' ← rs.toList.mapM (elabTerm · none)
    return (← elabTerm p none, rs')
  | _ => throwError "[parseUnivCad]: impossible"

@[tactic compute_root_set] def evalComputeRootSet : Tactic := fun stx => withMainContext do
  let (p, rs) ← parseComputeRootSet stx
  let roots_pfs ← rs.mapM (fun a => getSignProof p a)
  let rs_sorted ← genPfSortedLT rs
  let p_n_roots ← gen_root_counting_proof p
  let e ← computeSortedRootSet p rs p_n_roots rs_sorted roots_pfs
  closeMainGoal .anonymous e

def r3 : Rat := 3 / 2

open CPolynomial in
def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15

def r1 : Raw := ⟨p1, -3/2, -5/4⟩
def R1 : AlgNum := by lift_alg_num r1

def r2 : Raw := ⟨p1, 1, 5/4⟩
def R2 : AlgNum := by lift_alg_num r2

open CPolynomial in
def p' : CPolynomial Rat := 5 • X^2 + X - 15 / 2

lemma l5 : [R1.toReal, R2.toReal] = (toPolyReal p').roots.toFinset.sort := by compute_root_set p', [R1, R2]

lemma l3 : (toPolyReal p').roots.toFinset.card = 2 := by count_roots p'
lemma l3_2 : ((toPolyReal p').roots.toFinset.sort (· ≤ ·)).length = 2 := by
  have := l3
  rw [<- Finset.length_sort (α := Real) (s := (toPolyReal p').roots.toFinset) (· ≤ ·)] at this
  exact this

lemma l6 : ∀ x : Real, R1.toReal < x → x < R2.toReal → (toPolyReal p').eval x ≠ 0 := by
  intros x h1 h2
  have := no_roots_between_roots (toPolyReal p') (toPolyReal_zero p' (by decide +kernel)) 0 (by rw [l3_2]; decide)
  rw [<- l5] at this
  simp at this
  exact this x h1 h2

/- example (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by -/
/-   admit -/

end  main_tests
