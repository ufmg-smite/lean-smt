import Lean
import Lean.Meta.Tactic.Simp

import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.CountRoots
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

/-- A proof of `List.Sublist l₁ l₂` for explicit lists whose elements are compared syntactically:
`l₁` must be obtained from `l₂` by dropping elements. Linear in the length of `l₂`. -/
def mkSublistPf (α : Q(Type)) (l₁ l₂ : List Q($α)) : MetaM Expr :=
  match l₁, l₂ with
  | [], [] => pure q(List.Sublist.slnil (α := $α))
  | [], b :: l₂ => do
    let h ← mkSublistPf α [] l₂
    let l₂e : Q(List $α) := toListExpr α l₂
    let h : Q(List.Sublist [] $l₂e) := h
    pure q(List.Sublist.cons $b $h)
  | a :: l₁, b :: l₂ => do
    let l₁e : Q(List $α) := toListExpr α l₁
    let l₂e : Q(List $α) := toListExpr α l₂
    if a == b then
      let h : Q(List.Sublist $l₁e $l₂e) ← mkSublistPf α l₁ l₂
      pure q(List.Sublist.cons₂ $a $h)
    else
      let l₁e' : Q(List $α) := toListExpr α (a :: l₁)
      let h : Q(List.Sublist $l₁e' $l₂e) ← mkSublistPf α (a :: l₁) l₂
      pure q(List.Sublist.cons $b $h)
  | a :: _, [] => throwError "mkSublistPf: {a} is not an element of the larger list"

def computeSortedRootSet (p : Q(CPolynomial Rat)) (p_ne_0 : Expr) (rs_real : Q(List Real)) (roots_card rs_sorted : Expr) (roots_pfs : List Expr) : MetaM Expr := do
  let p_polyReal_ne_0' ← mkAppM ``toPolyReal_zero #[p, p_ne_0]
  let p_ne_0 ← mkAppM ``toPoly_ne0_of_poly_ne0 #[p, p_ne_0]

  let toPolyReal_rev ← mkAppM ``toPolyReal.eq_1 #[p]

  let hyp1 : Q(Prop) := q(List.length $rs_real = (toPolyReal $p).roots.toFinset.sort.length)
  let mv1 ← mkFreshExprMVar hyp1
  let hyp1_pf : Q($hyp1) := mv1
  let mv1? ← simp' mv1.mvarId! []
  match mv1? with
  | none => pure ()
  | some mv1' => let mv1' ← rewriteMVar mv1' roots_card; mv1'.refl

  let hyp2 : Q(Prop) := q(∀ i ∈ $rs_real, i ∈ (toPolyReal $p).roots.toFinset.sort (· ≤ ·))
  let mv2 ← mkFreshExprMVar hyp2
  let hyp2_pf := mv2
  let mv2? ← simp' mv2.mvarId! (p_ne_0 :: p_polyReal_ne_0' :: roots_pfs) []
  match mv2? with
  | none => pure ()
  | some mv2' => mv2'.assign p_polyReal_ne_0'

  let hyp3_pf := rs_sorted
  let hyp4_pf := q(Finset.sortedLT_sort (toPolyReal $p).roots.toFinset)
  mkAppM ``list_eq_of_sorted_of_length_of_mem #[rs_real, q((toPolyReal $p).roots.toFinset.sort (· ≤ ·)), hyp1_pf, hyp2_pf, hyp3_pf, hyp4_pf]

/-! The contradiction closing one cell of the decomposition: the sign of a polynomial on the
cell, established by the `sign_stops_*` lemmas (open cells) or by `getSignProof` (points),
against the constraint on that polynomial. Which polynomial is violated is found natively
(`sgnQ` of its value at the sample point, the relation of its constraint), so no search is
needed on the Lean side. -/

lemma contra_neg_ge {e : ℝ} (h : e < 0) (h' : e ≥ 0) : False := absurd h' (not_le.mpr h)
lemma contra_neg_gt {e : ℝ} (h : e < 0) (h' : e > 0) : False := absurd h' (not_lt.mpr (le_of_lt h))
lemma contra_neg_eq {e : ℝ} (h : e < 0) (h' : e = 0) : False := absurd h' (ne_of_lt h)
lemma contra_pos_le {e : ℝ} (h : e > 0) (h' : e ≤ 0) : False := absurd h' (not_le.mpr h)
lemma contra_pos_lt {e : ℝ} (h : e > 0) (h' : e < 0) : False := absurd h' (not_lt.mpr (le_of_lt h))
lemma contra_pos_eq {e : ℝ} (h : e > 0) (h' : e = 0) : False := absurd h' (ne_of_gt h)
lemma contra_zero_lt {e : ℝ} (h : e = 0) (h' : e < 0) : False := absurd (h ▸ h') (lt_irrefl 0)
lemma contra_zero_gt {e : ℝ} (h : e = 0) (h' : e > 0) : False := absurd (h ▸ h') (lt_irrefl 0)

/-- A polynomial whose sorted root list is empty has no real root. -/
lemma no_roots_of_sorted_empty (p : CPolynomial Rat) (hp : toPolyReal p ≠ 0)
    (h : ([] : List Real) = (toPolyReal p).roots.toFinset.sort (· ≤ ·)) :
    ∀ k : Real, ¬ (toPolyReal p).eval k = 0 := by
  intro k hk
  have hcard : (toPolyReal p).roots.toFinset.card = 0 := by
    have := congrArg List.length h
    simpa [Finset.length_sort] using this.symm
  rw [Finset.card_eq_zero] at hcard
  have hmem : k ∈ (toPolyReal p).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hk)
  rw [hcard] at hmem
  simp at hmem

/-- With no real root, a negative value forces a negative sign on the whole line. -/
lemma sign_stops_neg_line (x : ℝ) (p : Polynomial ℝ) (h_no_roots : ∀ k : ℝ, ¬ p.eval k = 0)
    (hx : p.eval x < 0) (y : ℝ) : p.eval y < 0 :=
  sign_stops_neg_pre x p (max x y + 1) (fun k _ => h_no_roots k)
    (by linarith [le_max_left x y]) hx y (by linarith [le_max_right x y])

/-- With no real root, a positive value forces a positive sign on the whole line. -/
lemma sign_stops_pos_line (x : ℝ) (p : Polynomial ℝ) (h_no_roots : ∀ k : ℝ, ¬ p.eval k = 0)
    (hx : p.eval x > 0) (y : ℝ) : p.eval y > 0 :=
  sign_stops_pos_pre x p (max x y + 1) (fun k _ => h_no_roots k)
    (by linarith [le_max_left x y]) hx y (by linarith [le_max_right x y])

/-- The relation of a constraint `cmp e 0`, as the head constant of its type. -/
def constraintRel (ineq_pf : Expr) : MetaM Name := do
  let t ← instantiateMVars (← inferType ineq_pf)
  match t.getAppFn with
  | .const n _ => pure n
  | _ => throwError "constraintRel: unexpected constraint {t}"

/-- The sign of `p` at a root value, computed natively (as `getSignProof` does). -/
def nativeSign (p : CPolynomial Rat) : RootVal → Int
  | .rat _ v => sgnC (p.eval v)
  | .alg _ a => seqVarSturmC_ab' a.p (a.p.derivative * p) a.l a.r

/-- The lemma refuting a constraint with relation `rel` on a polynomial whose sign is `s` on the
cell, if they are incompatible. -/
def contraLemma (s : Int) (rel : Name) : Option Name :=
  if s < 0 then
    if rel == ``GE.ge then some ``contra_neg_ge
    else if rel == ``GT.gt then some ``contra_neg_gt
    else if rel == ``Eq then some ``contra_neg_eq
    else none
  else if s > 0 then
    if rel == ``LE.le then some ``contra_pos_le
    else if rel == ``LT.lt then some ``contra_pos_lt
    else if rel == ``Eq then some ``contra_pos_eq
    else none
  else
    if rel == ``LT.lt then some ``contra_zero_lt
    else if rel == ``GT.gt then some ``contra_zero_gt
    else none

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

structure Data where
  poly : Q(CPolynomial Rat)
  poly_native : CPolynomial Rat
  poly_ne_0 : Q($poly ≠ 0)
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

lemma alg_midpoint_rr (R1 R2 : Rat) (h12 : R1 < R2) : ratToReal ((R1 + R2) / 2) ∈ Set.Ioo (ratToReal R1) (ratToReal R2) := by
  unfold ratToReal
  simp only [eq_ratCast, map_div₀, Rat.cast_add, Rat.cast_ofNat, Set.mem_Ioo]
  have : (↑R1 : Real) < R2 := by simp_all only [Rat.cast_lt]
  grind

lemma alg_midpoint_ra (R1 : Rat) (R2 : AlgNum) (h12 : R1 < R2.l) : ratToReal ((R1 + R2.l) / 2) ∈ Set.Ioo (ratToReal R1) R2.toReal := by
  unfold ratToReal
  simp
  have : (↑R1 : Real) < R2.l := by simp_all only [Rat.cast_lt]
  have : R2.l ≤ R2.toReal := (toReal_bounds R2).1
  grind

lemma alg_midpoint_ar (R1 : AlgNum) (R2 : Rat) (h12 : R1.r < R2) : ratToReal ((R1.r + R2) / 2) ∈ Set.Ioo R1.toReal (ratToReal R2) := by
  unfold ratToReal
  simp
  have : (↑R1.r : Real) < R2 := by simp_all only [Rat.cast_lt]
  have : R1.toReal ≤ R1.r := (toReal_bounds R1).2
  grind

lemma alg_midpoint_aa (R1 R2 : AlgNum) (h12 : R1.r < R2.l) : ratToReal ((R1.r + R2.l) / 2) ∈ Set.Ioo R1.toReal R2.toReal := by
  unfold ratToReal
  simp only [map_div₀, eq_ratCast, Rat.cast_add, Rat.cast_ofNat, Set.mem_Ioo]
  have : (R1.r : Real) < R2.l := by gcongr
  have : R1.toReal ≤ R1.r := (toReal_bounds R1).2
  have : R2.l ≤ R2.toReal := (toReal_bounds R2).1
  grind

lemma alg_pre (R : AlgNum) : ratToReal (R.l - 1) < R.toReal := by
  have : ratToReal R.l ≤ R.toReal := by
    unfold ratToReal ratToRealHom
    exact (toReal_bounds R).1
  have : ratToReal (R.l - 1) = ratToReal R.l - 1 := by
    unfold ratToReal
    norm_num
  rw [this]
  grind

lemma alg_pre' (R : Rat) :  ratToReal (R - 1) < ratToReal R := by
  unfold ratToReal
  norm_num

lemma alg_pos (R : AlgNum) : R.toReal < ratToReal (R.r + 1) := by
  have : R.toReal ≤ ratToReal R.r := by
    unfold ratToReal ratToRealHom
    exact (toReal_bounds R).2
  have : ratToReal (R.r + 1) = ratToReal R.r + 1 := by
    unfold ratToReal
    norm_num
  rw [this]
  grind

lemma alg_pos' (R : Rat) : ratToReal R < ratToReal (R + 1) := by
  unfold ratToReal
  norm_num

lemma cast_eval_neg {x : Rat} {p : CPolynomial Rat} (hpx : CPolynomial.eval x p < 0)
    : Polynomial.eval (ratToReal x) (toPolyReal p) < 0 := by
  unfold toPolyReal ratToReal ratToRealHom
  rw [eval_toPoly] at hpx
  have : (Rat.castHom Real (Polynomial.eval x p.toPoly)) < 0 := by
    simp_all only [eq_ratCast, Rat.cast_lt_zero]
  rwa [Polynomial.eval_map_apply]

lemma cast_eval_pos {x : Rat} {p : CPolynomial Rat} (hpx : CPolynomial.eval x p > 0)
    : Polynomial.eval (ratToReal x) (toPolyReal p) > 0 := by
  unfold toPolyReal ratToReal ratToRealHom
  rw [eval_toPoly] at hpx
  have : (Rat.castHom Real (Polynomial.eval x p.toPoly)) > 0 := by
    simp_all only [gt_iff_lt, eq_ratCast, Rat.cast_pos]
  rwa [Polynomial.eval_map_apply]

lemma sublist_sorted (l1 l2 : List Real) : l1.SortedLT → List.Sublist l2 l1 → l2.SortedLT := by
  intros h1 h2
  grind

-- Solves one of the intervals for univ_cad. Returns `some mv` if it is not supported yet
def solveCase (mv : MVarId) (idx N : Nat) (polys_ineqs_roots_subsets : Array Data) (all_roots_alg : List RootVal) (all_roots : Q(List Real)) (all_roots_sorted : Expr) (var : Q(Real)) : Smt.ReconstructM (Option MVarId) := do
  /- let solve_case_pre ← IO.monoMsNow -/
  let result ← if idx % 2 = 0 then -- interval
    if idx != 0 ∧ idx < 2 * N then
      let (fv, mv') ← mv.intro1P
      mv'.withContext do
        let var_inter ← mkAppM ``set_between #[.fvar fv]
        let L := all_roots_alg.getD ((idx - 2) / 2) default
        let R := all_roots_alg.getD ((idx - 2) / 2 + 1) default
        let Lr: Q(Rat) :=
          if L.isAlgNum then mkApp (mkConst ``AlgNum.r) L.expr else L.expr
        let Lr_native : Rat :=
          match L with
          | .alg _ a => a.r
          | .rat _ r => r
        let Rl: Q(Rat) :=
          if R.isAlgNum then mkApp (mkConst ``AlgNum.l) R.expr else R.expr
        let Rl_native : Rat :=
          match R with
          | .alg _ a => a.l
          | .rat _ r => r
        let mid: Q(Rat) := q(($Lr + $Rl) / 2)
        let mid_native : Rat := (Lr_native + Rl_native) / 2
        let lr_ord_prop : Q(Prop) := q($Lr < $Rl)
        let lr_ord ← mkDecideProof' lr_ord_prop
        let mid_mem ←
          if L.isAlgNum && R.isAlgNum then mkAppM ``alg_midpoint_aa #[L.expr, R.expr, lr_ord]
          else if L.isAlgNum && !R.isAlgNum then mkAppM ``alg_midpoint_ar #[L.expr, R.expr, lr_ord]
          else if !L.isAlgNum && R.isAlgNum then mkAppM ``alg_midpoint_ra #[L.expr, R.expr, lr_ord]
          else mkAppM ``alg_midpoint_rr #[L.expr, R.expr, lr_ord]

        let mut closed := false
        for ⟨poly, poly_native, p_ne_0, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
          -- the sign of `poly` on the cell: no root inside, so its sign at the midpoint
          let s := sgnQ (CPolynomial.eval mid_native poly_native)
          let some contra := contraLemma s (← constraintRel ineq_pf) | continue
          let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]
          let poly' ← mkAppM ``toPolyReal #[poly]
          let i:Q(Nat) := q(($idx - 2) / 2)
          let i_bound_prop : Q(Prop) := q($i < List.length $all_roots - 1)
          let mv_i_bound ← mkFreshExprMVar i_bound_prop
          normNum mv_i_bound.mvarId!
          let pf ← mkAppM ``no_roots_between_roots''
            #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted, i, mv_i_bound]
          let key ← if s < 0 then do
              let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $mid $poly < 0)
              let eval_neg ← mkDecideProof' eval_neg_prop
              let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
              mkAppM ``sign_stops_neg
                #[q(ratToReal $mid), poly', ← RootVal.toReal L, ← RootVal.toReal R, pf, mid_mem, eval_neg_real, var, var_inter]
            else do
              let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $mid $poly > 0)
              let eval_pos ← mkDecideProof' eval_pos_prop
              let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
              mkAppM ``sign_stops_pos
                #[q(ratToReal $mid), poly', ← RootVal.toReal L, ← RootVal.toReal R, pf, mid_mem, eval_pos_real, var, var_inter]
          mv'.assign (← mkAppM contra #[key, ineq_pf])
          closed := true
          break
        unless closed do throwError "solveCase: no constraint is violated on cell {idx}"
      pure none
    else
      if idx == 0 then
        let (fv, mv') ← mv.intro1P
        mv'.withContext do
          let var_pre ← mkAppM ``set_before #[.fvar fv]
          let R := all_roots_alg.getD 0 default
          let Rl: Q(Rat) := if R.isAlgNum then (mkApp (mkConst ``AlgNum.l) R.expr) else R.expr
          let Rl_native : Rat :=
            match R with
            | .alg _ a => a.l
            | .rat _ v => v
          let pre: Q(Rat) := q($Rl - 1)
          let pre_native := Rl_native - 1
          let pre_mem ←
            if R.isAlgNum then mkAppM ``alg_pre #[R.expr]
            else mkAppM ``alg_pre' #[R.expr]

          let mut closed := false
          for ⟨poly, poly_native, p_ne_0, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
            let s := sgnQ (CPolynomial.eval pre_native poly_native)
            let some contra := contraLemma s (← constraintRel ineq_pf) | continue
            let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]
            let poly' ← mkAppM ``toPolyReal #[poly]
            let pf ← mkAppM ``no_roots_before_first'' #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted]
            let key ← if s < 0 then do
                let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $pre $poly < 0)
                let eval_neg ← mkDecideProof' eval_neg_prop
                let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
                mkAppM ``sign_stops_neg_pre #[q(ratToReal $pre), poly', ← RootVal.toReal R, pf, pre_mem, eval_neg_real, var, var_pre]
              else do
                let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $pre $poly > 0)
                let eval_pos ← mkDecideProof' eval_pos_prop
                let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
                mkAppM ``sign_stops_pos_pre #[q(ratToReal $pre), poly', ← RootVal.toReal R, pf, pre_mem, eval_pos_real, var, var_pre]
            mv'.assign (← mkAppM contra #[key, ineq_pf])
            closed := true
            break
          unless closed do throwError "solveCase: no constraint is violated before the first root"
        pure none
      else
        let (fv, mv') ← mv.intro1P
        mv'.withContext do
          let var_pos ← mkAppM ``set_after #[.fvar fv]
          let L := all_roots_alg.getLast!
          let Lr : Q(Rat) := if L.isAlgNum then mkApp (mkConst ``AlgNum.r) L.expr else L.expr
          let Lr_native : Rat :=
            match L with
            | .rat _ r => r
            | .alg _ a => a.r
          let pos: Q(Rat) := q($Lr + 1)
          let pos_native := Lr_native + 1
          let pos_mem ←
            if L.isAlgNum then mkAppM ``alg_pos #[L.expr]
            else mkAppM ``alg_pos' #[L.expr]

          let mut closed := false
          for ⟨poly, poly_native, p_ne_0, ineq_pf, roots, roots_pf, subset⟩ in polys_ineqs_roots_subsets do
            let s := sgnQ (CPolynomial.eval pos_native poly_native)
            let some contra := contraLemma s (← constraintRel ineq_pf) | continue
            let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]
            let poly' ← mkAppM ``toPolyReal #[poly]
            let pf ← mkAppM ``no_roots_after_last'' #[poly', p_polyReal_ne_0, all_roots, roots, roots_pf, subset, all_roots_sorted]
            let key ← if s < 0 then do
                let eval_neg_prop : Q(Prop) := q(CPolynomial.eval $pos $poly < 0)
                let eval_neg ← mkDecideProof' eval_neg_prop
                let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
                mkAppM ``sign_stops_neg_pos #[q(ratToReal $pos), poly', ← RootVal.toReal L, pf, pos_mem, eval_neg_real, var, var_pos]
              else do
                let eval_pos_prop : Q(Prop) := q(CPolynomial.eval $pos $poly > 0)
                let eval_pos ← mkDecideProof' eval_pos_prop
                let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
                mkAppM ``sign_stops_pos_pos #[q(ratToReal $pos), poly', ← RootVal.toReal L, pf, pos_mem, eval_pos_real, var, var_pos]
            mv'.assign (← mkAppM contra #[key, ineq_pf])
            closed := true
            break
          unless closed do throwError "solveCase: no constraint is violated after the last root"
        pure none
  else
    let (fv, mv') ← mv.intro1P
    mv'.withContext do
      let var_val ← mkAppM ``set_eq #[.fvar fv]
      let r := all_roots_alg.getD ((idx - 1) / 2) default
      let mut closed := false
      for ⟨poly, poly_native, _, ineq, _, _, _⟩ in polys_ineqs_roots_subsets do
        let s := nativeSign poly_native r
        let some contra := contraLemma s (← constraintRel ineq) | continue
        let ineq' ← rewriteWithEq ineq var_val
        let (poly_sign, _) ← getSignProof poly poly_native r
        mv'.assign (← mkAppM contra #[poly_sign, ineq'])
        closed := true
        break
      unless closed do throwError "solveCase: no constraint is violated at root {idx}"
    pure none
  /- let solve_case_pos ← IO.monoMsNow -/
  /- logInfo m!"current solve case: {solve_case_pos - solve_case_pre}ms" -/
  return result

def univCadCore (x : Q(Real)) (ineq_pfs : List Expr) (rs : List RootVal) : Smt.ReconstructM (Expr × List MVarId) := do
  let rs ← rs.mapM fun rv => do
    let e' ← hoistExpr `_univCadRoot rv.expr
    match rv with
    | .rat _ v => return RootVal.rat e' v
    | .alg _ raw => return RootVal.alg e' raw
  let (rs_sorted, rs) ← genPfSortedLT rs
  /- let sort_after ← IO.monoMsNow -/
  let mut polys_ineqs_roots_subsets : Array Data := #[]
  let rs_real : List Q(Real) ← rs.mapM RootVal.toReal
  let rs_e := toListExpr q(Real) rs_real
  for ineq_pf in ineq_pfs do
    /- let curr_ineq_pre ← IO.monoMsNow -/
    let (P_inline, P_native, ineq_pf_P) ← lift_ineq ineq_pf x
    let P : Q(CPolynomial Rat) ← hoistExpr `_univCadPoly P_inline
    -- Retype `ineq_pf_P` so its type mentions the hoisted `P` instead of the
    -- original inline polynomial. Since the aux decl is `.abbrev`, the two are
    -- definitionally equal, but rewriting the type explicitly keeps downstream
    -- tactics (notably `grind`) from having to unfold on the fly.
    let ineq_pf_P_t ← inferType ineq_pf_P
    let ineq_pf_P_t' := ineq_pf_P_t.replace fun e => if e == P_inline then some P else none
    let ineq_pf_P ← mkExpectedTypeHint ineq_pf_P ineq_pf_P_t'

    let P_roots_card ← gen_root_counting_proof P P_native
    let mut root_pfs : Array Expr := #[]
    let mut curr_roots : Array RootVal := #[]
    for r in rs do
      let (sign_pf, sign) ← getSignProof P P_native r
      if sign = 0 then
        curr_roots := curr_roots.push r
        root_pfs := root_pfs.push sign_pf

    let curr_roots_e := toListExpr q(Real) (← curr_roots.toList.mapM RootVal.toReal)
    -- `curr_roots` is a subsequence of `rs` made of the same expressions, so the proof is a
    -- walk along both lists with the `Sublist` constructors. (`norm_num` on this goal took up
    -- to 37s per inequality on lists of 13 algebraic roots.)
    let mv_sublist ← mkSublistPf q(Real) (← curr_roots.toList.mapM RootVal.toReal) rs_real
    let pf_subset ← mkAppM ``List.Sublist.subset #[mv_sublist]
    let curr_roots_sorted ← mkAppM ``sublist_sorted #[rs_e, curr_roots_e, rs_sorted, mv_sublist]

    let P_ne_0_goal := q($P ≠ 0)
    let P_ne_0 ← mkDecideProof' P_ne_0_goal
    let roots_description ← computeSortedRootSet P P_ne_0 curr_roots_e P_roots_card curr_roots_sorted root_pfs.toList
    polys_ineqs_roots_subsets := polys_ineqs_roots_subsets.push (Data.mk P P_native P_ne_0 ineq_pf_P curr_roots_e roots_description pf_subset)
    /- let curr_ineq_pos ← IO.monoMsNow -/
    /- logInfo m!"reconstructing inequality: {curr_ineq_pos - curr_ineq_pre}ms" -/

  /- let all_ineq_pos ← IO.monoMsNow -/
  /- logInfo m!"accumulated of reconstructing inequalities: {all_ineq_pos - sort_after}ms" -/
  if rs.isEmpty then
    -- No polynomial has a real root, so each has a constant sign on the whole line, and the
    -- sign at 0 of some polynomial violates its constraint.
    for ⟨poly, poly_native, p_ne_0, ineq_pf, _, roots_pf, _⟩ in polys_ineqs_roots_subsets do
      let s := sgnQ (CPolynomial.eval 0 poly_native)
      let some contra := contraLemma s (← constraintRel ineq_pf) | continue
      let p_polyReal_ne_0 ← mkAppM ``toPolyReal_zero #[poly, p_ne_0]
      let poly' ← mkAppM ``toPolyReal #[poly]
      let no_roots ← mkAppM ``no_roots_of_sorted_empty #[poly, p_polyReal_ne_0, roots_pf]
      let zero : Q(Rat) := q(0)
      let key ← if s < 0 then do
          let eval_neg ← mkDecideProof' q(CPolynomial.eval $zero $poly < 0)
          let eval_neg_real ← mkAppM ``cast_eval_neg #[eval_neg]
          mkAppM ``sign_stops_neg_line #[q(ratToReal $zero), poly', no_roots, eval_neg_real, x]
        else do
          let eval_pos ← mkDecideProof' q(CPolynomial.eval $zero $poly > 0)
          let eval_pos_real ← mkAppM ``cast_eval_pos #[eval_pos]
          mkAppM ``sign_stops_pos_line #[q(ratToReal $zero), poly', no_roots, eval_pos_real, x]
      return (← mkAppM contra #[key, ineq_pf], [])
    throwError "univCadCore: no real roots, but no constraint is violated"
  let decomp_pf ← getDecompPf x rs_e rs_sorted
  let decomp_after ← IO.monoMsNow
  /- logInfo m!"getting decoposition proof: {decomp_after - all_ineq_pos}ms" -/

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
  let joining_decomps_after ← IO.monoMsNow
  logInfo m!"joining proofs for each interval: {joining_decomps_after - decomp_after}ms"

  let indexedGoals := disjunctsToFalseMvs.zipIdx
  let unsolvedMvs ← indexedGoals.mapM (fun (e, i) => solveCase e.mvarId! i rs.length polys_ineqs_roots_subsets rs rs_e rs_sorted x)
  let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) []

  let accumulated_intervals_pos ← IO.monoMsNow
  logInfo m!"accumulated of solving each interval: {accumulated_intervals_pos - joining_decomps_after}ms"

  return (answer, unsolvedMvs)

/- @[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do -/
/-   let (x, ineq_pfs, rs) ← parseUnivCad stx -/
/-   let rvs ← (rs.mapM RootVal.ofExpr : MetaM (List RootVal)) -/
/-   let e ← univCadCore false x ineq_pfs rvs -/
/-   let mainMv ← getMainGoal -/
/-   mainMv.assign e.1 -/
/-   replaceMainGoal e.2 -/

/- namespace main_tests -/

/- def a : Rat := -9 -/
/- def b : Rat := 0 -/
/- def c : Rat := 10 -/

/- lemma ex1 (x : Real) (h1 : x ≥ -9) (h2 : x < 10) (h3 : x * x * x * x > 0) (h4: (x * x * x * x * x * x * x * x ≤ 0)) : False := by -/
/-   univ_cad x , [h1,h2,h3,h4] [a,b,c] -/

/- def p2 : CPolynomial Rat := X - 3/2 -/
/- def r3 : Raw := ⟨p2, 7/5, 2⟩ -/
/- def R3 : AlgNum := by lift_alg_num r3 -/

/- abbrev R3' : Rat := 3 / 2 -/

/- def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15 -/

/- def r1 : Raw := ⟨p1, -4/2, -6/4⟩ -/
/- def R1 : AlgNum := by lift_alg_num r1 -/

/- def r2 : Raw := ⟨p1, 1, 5/4⟩ -/
/- def R2 : AlgNum := by lift_alg_num r2 -/

/- lemma exemplo (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by -/
/-   univ_cad a, [h1, h2] [R1, R2, R3'] -/

/- #print axioms exemplo -/

/- def zero_p : CPolynomial Rat := X -/
/- def zero_r : Raw := ⟨zero_p, -1, 1⟩ -/
/- def zero : AlgNum := by lift_alg_num zero_r -/

/- example (x : Real) (h1 : x * x * x * x * x > 0) (h2 : x * x * x < 0) : False := by -/
/-   univ_cad x, [h1, h2] [zero] -/

/- end main_tests -/
