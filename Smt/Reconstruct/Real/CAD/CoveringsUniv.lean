import Lean
import Lean.Meta.Tactic.Simp

import Smt.Reconstruct.Real.CAD.CountRoots
import Smt.Reconstruct.Real.CAD.CPolynomial
import Smt.Reconstruct.Real.CAD.LiftIneq
import Smt.Reconstruct.Real.CAD.NormalizePoly
import Smt.Reconstruct.Real.CAD.Split
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign

open Qq Lean Elab Tactic Meta

open CompPoly
open CPolynomial

open AlgebraicNumber

--                                   inequality proofs  roots
syntax (name := univ_cad) "univ_cad" term "," ("[" term,* "]")   ("[" term,* "]") : tactic

def parseUnivCad : Syntax → TacticM (Expr × List Expr × List Q(AlgNum))
  | `(tactic| univ_cad $x , [ $[$as],* ] [ $[$bs],* ] ) => do
    let as' ← as.toList.mapM (elabTerm · none)
    let bs' ← bs.toList.mapM (elabTerm · none)
    let x' ← elabTerm x none
    return (x', as', bs')
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

lemma set_eq {x y : Real} : (x ∈ setOf (fun z => z = y)) -> x = y := by
  intro h
  finiteness

def get_r (r : Expr) : MetaM Expr := do
  match r with
  | .app (.const ``AlgNum.toReal []) x => return x
  | _ => panic! "impossible"

-- Solves one of the intervals for univ_cad. Returns `some mv` if it is not supported yet
def solveCase (mv : MVarId) (idx : Nat) (polys_ineqs_roots : Array (Expr × Expr × Expr)) : MetaM (Option MVarId) := do
  if idx % 2 = 0 then -- interval
    return mv
  else
    let (fv, mv') ← mv.intro1P
    mv'.withContext do
      let var_val ← mkAppM ``set_eq #[.fvar fv]
      let var_val_t ← inferType var_val
      let some (_,_,r) := var_val_t.eq? | throwError "impossible"
      let mut grind_context : Array Expr := #[]
      for (poly, ineq, _) in polys_ineqs_roots do
        let ineq' ← rewriteWithEq ineq var_val
        let (poly_sign, _) ← getSignProof poly (← get_r r)
        grind_context := grind_context.push poly_sign
        grind_context := grind_context.push ineq'
      runGrind' mv' grind_context.toList
    return none

def univCadCore (x : Q(Real)) (ineq_pfs : List Expr) (rs : List Q(AlgNum)) : MetaM (Expr × List MVarId) := do
  let rs_sorted ← genPfSortedLT rs
  let mut polys_ineqs_roots : Array (Expr × Expr × Expr) := #[]
  for ineq_pf in ineq_pfs do
    let (P, ineq_pf_P) ← lift_ineq ineq_pf
    let P_roots_card ← gen_root_counting_proof P
    let mut root_pfs : Array Expr := #[]
    let mut curr_roots : Array Expr := #[]
    for r in rs do
      let (sign_pf, sign) ← getSignProof P r
      if sign = 0 then
        curr_roots := curr_roots.push r
        root_pfs := root_pfs.push sign_pf
    let curr_roots_sorted ← genPfSortedLT curr_roots.toList
    let roots_description ← computeSortedRootSet P curr_roots.toList P_roots_card curr_roots_sorted root_pfs.toList
    polys_ineqs_roots := polys_ineqs_roots.push (P, ineq_pf_P, roots_description)

  let decomp_pf ← getDecompPf x rs rs_sorted
  let mv ← mkFreshExprMVar (mkConst ``False)
  let congrTheorems ← getSimpCongrTheorems
  let simpTheorems ← getSimpTheorems
  let simpTheoremsArray : SimpTheoremsArray := #[simpTheorems]
  let ctx ← Simp.mkContext (simpTheorems := simpTheoremsArray) (congrTheorems := congrTheorems)
  let (some (decomp_pf', t'), _) ← simpStep mv.mvarId! decomp_pf (← inferType decomp_pf) ctx | throwError "impossible"
  let disjuncts := collectDisjuncts t'
  let disjunctsToFalse ← disjuncts.mapM (mkArrow · q(False))
  let disjunctsToFalseMvs ← disjunctsToFalse.mapM (fun e => Meta.mkFreshExprMVar e)
  let answer ← go disjunctsToFalseMvs decomp_pf'

  let indexedGoals := disjunctsToFalseMvs.zipIdx
  let unsolvedMvs ← indexedGoals.mapM (fun (e, i) => solveCase e.mvarId! i polys_ineqs_roots)
  let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) []

  return (answer, unsolvedMvs)

-- For now I'm assuming all roots are AlgNum's (but they will be either rational or AlgNum)
@[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do
  let (x, ineq_pfs, rs) ← parseUnivCad stx
  let e ← univCadCore x ineq_pfs rs
  let mainMv ← getMainGoal
  mainMv.assign e.1
  replaceMainGoal e.2

def p2 : CPolynomial Rat := X - 3/2
def r3 : Raw := ⟨p2, 1, 2⟩
def R3 : AlgNum := by lift_alg_num r3

def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15

def r1 : Raw := ⟨p1, -3/2, -5/4⟩
def R1 : AlgNum := by lift_alg_num r1

def r2 : Raw := ⟨p1, 1, 5/4⟩
def R2 : AlgNum := by lift_alg_num r2


example (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by
  univ_cad a, [h1, h2] [R1, R2, R3]
  · admit
  · admit
  · admit
  · admit


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
  let e ← computeSortedRootSet p rs p_n_roots rs_sorted (roots_pfs.map (fun x => x.1))
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


end  main_tests
