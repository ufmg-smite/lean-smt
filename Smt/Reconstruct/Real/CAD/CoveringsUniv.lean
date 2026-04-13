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
  let mv1? ← simp' mv1.mvarId! []
  match mv1? with
  | none => pure ()
  | some mv1' => let mv1' ← rewriteMVar mv1' roots_card; mv1'.refl

  let hyp2 : Q(Prop) := q(∀ i ∈ $rs_real', i ∈ (toPolyReal $p).roots.toFinset.sort (· ≤ ·))
  let mv2 ← mkFreshExprMVar hyp2
  let hyp2_pf := mv2
  let mv2? ← simp' mv2.mvarId! (p_ne_0 :: roots_pfs)
  match mv2? with
  | none => pure ()
  | some mv2' => mv2'.assign p_polyReal_ne_0'

  let hyp3_pf := rs_sorted
  let hyp4_pf := q(Finset.sortedLT_sort (toPolyReal $p).roots.toFinset)
  mkAppM ``list_eq_of_sorted_of_length_of_mem #[rs_real', q((toPolyReal $p).roots.toFinset.sort (· ≤ ·)), hyp1_pf, hyp2_pf, hyp3_pf, hyp4_pf]

lemma set_eq {x y : Real} : (x ∈ setOf (fun z => z = y)) -> x = y := by
  intro h
  finiteness

lemma set_between {x y z : Real} : (x ∈ setOf (fun w => y < w ∧ w < z)) -> x ∈ Set.Ioo y z := by
  intro h
  finiteness

lemma set_before {x y : Real} : (x ∈ setOf (fun w => w < y)) -> x < y := by
  intro h
  finiteness

lemma set_after {x y : Real} : (x ∈ setOf (fun w => y < w)) -> y < x := by
  intro h
  finiteness

def get_r (r : Expr) : MetaM Expr := do
  match r with
  | .app (.const ``AlgNum.toReal []) x => return x
  | _ => panic! "impossible"

structure Data where
  poly : Q(CPolynomial Rat)
  ineq_pf : Expr
  roots : Q(List AlgNum)
  roots_pf : Expr
  subset : Expr

def sgnQ (q : Rat) : Int :=
  if q < 0 then -1 else if q = 0 then 0 else 1

lemma sgn_sgn_negQ : ∀ x : Rat, sgnQ x < 0 ↔ x < 0 := by
  intro x
  unfold sgnQ
  split_ifs <;> grind

lemma sgn_sgn_posQ : ∀ x : Rat, sgnQ x > 0 ↔ x > 0 := by
  intro x
  unfold sgnQ
  split_ifs <;> grind

lemma alg_midpoint (R1 R2 : AlgNum) (h12 : R1.r < R2.l) : (Rat.castHom ℝ) ((R1.r + R2.l) / 2) ∈ Set.Ioo R1.toReal R2.toReal := by
  simp only [map_div₀, eq_ratCast, Rat.cast_add, Rat.cast_ofNat, Set.mem_Ioo]
  have : (R1.r : Real) < R2.l := by gcongr
  have : R1.toReal ≤ R1.r := (toReal_bounds R1).2
  have : R2.l ≤ R2.toReal := (toReal_bounds R2).1
  grind

lemma alg_pre (R : AlgNum) : (Rat.castHom ℝ) (R.l - 1) < R.toReal := by
  have : Rat.castHom Real R.l ≤ R.toReal := (toReal_bounds R).1
  have : Rat.castHom Real (R.l - 1) = Rat.castHom Real R.l - 1 := by norm_num
  rw [this]
  grind

lemma alg_pos (R : AlgNum) : R.toReal < (Rat.castHom ℝ) (R.r + 1) := by
  have : R.toReal ≤ Rat.castHom Real R.r := (toReal_bounds R).2
  have : Rat.castHom Real (R.r + 1) = Rat.castHom Real R.r + 1 := by norm_num
  rw [this]
  grind

lemma cast_eval_neg {x : Rat} {p : CPolynomial Rat} (hpx : CPolynomial.eval x p < 0)
    : Polynomial.eval (Rat.castHom Real x) (toPolyReal p) < 0 := by
  unfold toPolyReal
  rw [eval_toPoly] at hpx
  have : (Rat.castHom Real (Polynomial.eval x p.toPoly)) < 0 := by
    simp_all only [eq_ratCast, Rat.cast_lt_zero]
  rwa [Polynomial.eval_map_apply]

lemma cast_eval_pos {x : Rat} {p : CPolynomial Rat} (hpx : CPolynomial.eval x p > 0)
    : Polynomial.eval (Rat.castHom Real x) (toPolyReal p) > 0 := by
  unfold toPolyReal
  rw [eval_toPoly] at hpx
  have : (Rat.castHom Real (Polynomial.eval x p.toPoly)) > 0 := by
    simp_all only [gt_iff_lt, eq_ratCast, Rat.cast_pos]
  rwa [Polynomial.eval_map_apply]

-- Solves one of the intervals for univ_cad. Returns `some mv` if it is not supported yet
def solveCase (mv : MVarId) (idx N : Nat) (polys_ineqs_roots_subsets : Array Data) (all_roots_alg : List Q(AlgNum)) (all_roots : Q(List Real)) (all_roots_sorted : Expr) (var : Q(Real)) : MetaM (Option MVarId) := do
  if idx % 2 = 0 then -- interval
    if idx != 0 ∧ idx < 2 * N then
      let (fv, mv') ← mv.intro1P
      mv'.withContext do
        let var_inter ← mkAppM ``set_between #[.fvar fv]
        let L := all_roots_alg.getD ((idx - 2) / 2) (mkConst `Nat)
        let R := all_roots_alg.getD ((idx - 2) / 2 + 1) (mkConst `Nat)
        let mid: Q(Rat) := q((AlgNum.r $L + AlgNum.l $R) / 2)
        let lr_ord_prop : Q(Prop) := q(AlgNum.r $L < AlgNum.l $R)
        let lr_ord ← mkDecideProof lr_ord_prop
        let mid_mem ← mkAppM ``alg_midpoint #[L, R, lr_ord]

        let mut grind_context : Array Expr := #[]
        for ⟨poly, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
          -- TODO do not recompute this
          let p_ne_0_goal : Q(Prop) := q($poly ≠ 0)
          let p_ne_0 ← mkDecideProof p_ne_0_goal
          let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]

          let poly' ← mkAppM ``toPolyReal #[poly]
          let i:Q(Nat) := q(($idx - 2) / 2)
          let i_bound_prop : Q(Prop) := q($i < List.length $all_roots - 1)
          let mv_i_bound ← mkFreshExprMVar i_bound_prop
          let ok ← runGrind mv_i_bound.mvarId!
          if !ok then
            throwError m!"grind failed 1"
          let pf ← mkAppM ``no_roots_between_roots''
            #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted, i, mv_i_bound]

          let p_sgn: Q(Int) := q(sgnQ (CPolynomial.eval $mid $poly))
          let p_sgn_rfl ← unsafe evalExpr Int q(Int) p_sgn
          if p_sgn_rfl < 0 then
            let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $mid $poly < 0)
            let eval_neg ← mkDecideProof eval_neg_prop
            let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]

            let key ← mkAppM ``sign_stops_neg
              #[q(Rat.castHom Real $mid), poly', q(AlgNum.toReal $L), q(AlgNum.toReal $R), pf, mid_mem, eval_neg_real, var, var_inter]
            -- TODO: Could be just check if they are proving different signs and apply custom lemma
            grind_context := grind_context.push key
            grind_context := grind_context.push ineq_pf
          else
            let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $mid $poly > 0)
            let eval_pos ← mkDecideProof eval_pos_prop
            let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]

            let key ← mkAppM ``sign_stops_pos
              #[q(Rat.castHom Real $mid), poly', q(AlgNum.toReal $L), q(AlgNum.toReal $R), pf, mid_mem, eval_pos_real, var, var_inter]
            -- TODO: Could be just check if they are proving different signs and apply custom lemma
            grind_context := grind_context.push key
            grind_context := grind_context.push ineq_pf
        let ok ← runGrind' mv' grind_context.toList
        if !ok then
          throwError "grind failed 2"
      return none
    else
      if idx == 0 then
        let (fv, mv') ← mv.intro1P
        mv'.withContext do
          let var_pre ← mkAppM ``set_before #[.fvar fv]
          let R := all_roots_alg.getD 0 (mkConst `Nat)
          let pre: Q(Rat) := q(AlgNum.l $R - 1)
          let pre_mem ← mkAppM ``alg_pre #[R]

          let mut grind_context : Array Expr := #[]
          for ⟨poly, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
            -- TODO do not recompute this
            let p_ne_0_goal : Q(Prop) := q($poly ≠ 0)
            let p_ne_0 ← mkDecideProof p_ne_0_goal
            let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]

            let poly' ← mkAppM ``toPolyReal #[poly]
            let pf ← mkAppM ``no_roots_before_first'' #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted]

            let p_sgn: Q(Int) := q(sgnQ (CPolynomial.eval $pre $poly))
            let p_sgn_rfl ← unsafe evalExpr Int q(Int) p_sgn
            if p_sgn_rfl < 0 then
              let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $pre $poly < 0)
              let eval_neg ← mkDecideProof eval_neg_prop
              let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
              let key ← mkAppM ``sign_stops_neg_pre #[q(Rat.castHom Real $pre), poly', q(AlgNum.toReal $R), pf, pre_mem, eval_neg_real, var, var_pre]
              grind_context := grind_context.push key
              grind_context := grind_context.push ineq_pf
            else
              let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $pre $poly > 0)
              let eval_pos ← mkDecideProof eval_pos_prop
              let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
              let key ← mkAppM ``sign_stops_pos_pre #[q(Rat.castHom Real $pre), poly', q(AlgNum.toReal $R), pf, pre_mem, eval_pos_real, var, var_pre]
              grind_context := grind_context.push key
              grind_context := grind_context.push ineq_pf
          let ok ← runGrind' mv' grind_context.toList
          if !ok then
            throwError "grind failed 3"
        return none
      else
        let (fv, mv') ← mv.intro1P
        mv'.withContext do
          let var_pos ← mkAppM ``set_after #[.fvar fv]
          let L := all_roots_alg.getLast!
          let pos: Q(Rat) := q(AlgNum.r $L + 1)
          let pos_mem ← mkAppM ``alg_pos #[L]

          let mut grind_context : Array Expr := #[]
          for ⟨poly, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
            -- TODO do not recompute this
            let p_ne_0_goal : Q(Prop) := q($poly ≠ 0)
            let p_ne_0 ← mkDecideProof p_ne_0_goal
            let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]

            let poly' ← mkAppM ``toPolyReal #[poly]
            let pf ← mkAppM ``no_roots_after_last'' #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted]

            let p_sgn: Q(Int) := q(sgnQ (CPolynomial.eval $pos $poly))
            let p_sgn_rfl ← unsafe evalExpr Int q(Int) p_sgn
            if p_sgn_rfl < 0 then
              let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $pos $poly < 0)
              let eval_neg ← mkDecideProof eval_neg_prop
              let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
              let key ← mkAppM ``sign_stops_neg_pos #[q(Rat.castHom Real $pos), poly', q(AlgNum.toReal $L), pf, pos_mem, eval_neg_real, var, var_pos]
              grind_context := grind_context.push key
              grind_context := grind_context.push ineq_pf
            else
              let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $pos $poly > 0)
              let eval_pos ← mkDecideProof eval_pos_prop
              let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
              let key ← mkAppM ``sign_stops_pos_pos #[q(Rat.castHom Real $pos), poly', q(AlgNum.toReal $L), pf, pos_mem, eval_pos_real, var, var_pos]
              grind_context := grind_context.push key
              grind_context := grind_context.push ineq_pf
          let ok ← runGrind' mv' grind_context.toList
          if !ok then
            throwError "grind failed 4"
        return none
  else
    let (fv, mv') ← mv.intro1P
    mv'.withContext do
      let var_val ← mkAppM ``set_eq #[.fvar fv]
      let var_val_t ← inferType var_val
      let some (_,_,r) := var_val_t.eq? | throwError "impossible"
      let mut grind_context : Array Expr := #[]
      for ⟨poly, ineq, _, _, _⟩ in polys_ineqs_roots_subsets do
        let ineq' ← rewriteWithEq ineq var_val
        let (poly_sign, _) ← getSignProof poly (← get_r r)
        -- TODO: Could be just check if they are proving different signs and apply custom lemma
        grind_context := grind_context.push poly_sign
        grind_context := grind_context.push ineq'
      let ok ← runGrind' mv' grind_context.toList
      if !ok then
        throwError "grind failed 5"
    return none

def univCadCore (x : Q(Real)) (ineq_pfs : List Expr) (rs : List Q(AlgNum)) : MetaM (Expr × List MVarId) := do
  let rs_sorted ← genPfSortedLT rs
  let mut polys_ineqs_roots_subsets : Array Data := #[]
  let rs_real : List Q(Real) := rs.map (fun r => q(AlgNum.toReal $r))
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

    let curr_roots_e := toListExpr q(Real) (curr_roots.toList.map (fun r: Q(AlgNum) => q(AlgNum.toReal $r)))
    let rs_e := toListExpr q(Real) rs_real
    let curr_roots_subset_prop : Q(Prop) := q($curr_roots_e ⊆ $rs_e)
    let mv_subset ← mkFreshExprMVar curr_roots_subset_prop
    normNum mv_subset.mvarId!

    let roots_description ← computeSortedRootSet P curr_roots.toList P_roots_card curr_roots_sorted root_pfs.toList
    polys_ineqs_roots_subsets := polys_ineqs_roots_subsets.push (Data.mk P ineq_pf_P curr_roots_e roots_description mv_subset)

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
  let unsolvedMvs ← indexedGoals.mapM (fun (e, i) => solveCase e.mvarId! i rs.length polys_ineqs_roots_subsets rs (toListExpr q(Real) rs_real) rs_sorted x)
  let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) []

  return (answer, unsolvedMvs)

-- For now I'm assuming all roots are AlgNum's (but they will be either rational or AlgNum)
@[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do
  let (x, ineq_pfs, rs) ← parseUnivCad stx
  let e ← univCadCore x ineq_pfs rs
  let mainMv ← getMainGoal
  mainMv.assign e.1
  replaceMainGoal e.2

namespace main_tests

def p2 : CPolynomial Rat := X - 3/2
def r3 : Raw := ⟨p2, 7/5, 2⟩
def R3 : AlgNum := by lift_alg_num r3

def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15

def r1 : Raw := ⟨p1, -3/2, -5/4⟩
def R1 : AlgNum := by lift_alg_num r1

def r2 : Raw := ⟨p1, 1, 5/4⟩
def R2 : AlgNum := by lift_alg_num r2

lemma exemplo (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by
  univ_cad a, [h1, h2] [R1, R2, R3]

def zero_p : CPolynomial Rat := X
def zero_r : Raw := ⟨zero_p, -1, 1⟩
def zero : AlgNum := by lift_alg_num zero_r

example (x : Real) (h1 : x * x * x * x * x > 0) (h2 : x * x * x < 0) : False := by
  univ_cad x, [h1, h2] [zero]

#print axioms exemplo

end  main_tests
