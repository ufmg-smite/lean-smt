import Mathlib
import CompPoly
import Smt.Reconstruct.Real.CAD.Sturm.SturmSeq

open Polynomial

namespace Theorem

theorem sturm_tarski_interval (a b : ℝ) (p q : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    tarskiQuery p q a b = seqVarSturm_ab p (derivative p * q) a b := by
  rw [cauchyIndex_sturmSeq p (derivative p * q) a b hpa hpb hab]
  rw [cauchyIndex_poly_taq p q a b]

open CompPoly
open CPolynomial

theorem gneg_imp_gtopoly_neg (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
  intro abs
  have : g = 0 := by
    apply CPolynomial.eq_zero_iff_coeff_zero.mpr
    have aux (x : ℚ) := CPolynomial.eval_toPoly x g
    rw[abs] at aux
    simp at aux
    simp only [CPolynomial.coeff_toPoly]
    rw[abs]
    apply Polynomial.coeff_zero
  exact h this

instance : DecidableEq (CPolynomial.Raw Rat) := instDecidableEqOfLawfulBEq

instance : DecidableEq (CPolynomial Rat) := Subtype.instDecidableEq

theorem gtopolyzeroeq2 (g : CPolynomial ℚ) : g.toPoly ≠ 0 → g ≠ 0 := by
  contrapose
  intro h; rw[h]; exact toPoly_zero

theorem gtopolyzeroeq (g : CPolynomial ℚ) : g.toPoly = 0 → g = 0 := by
  contrapose
  apply gneg_imp_gtopoly_neg

theorem fg_mod_eq (f g : CPolynomial ℚ) : (f % g).toPoly = f.toPoly % g.toPoly := by
  have aux := CPolynomial.mod_toPoly f g
  have : (f.mod g) = f%g := by
    exact eq_iff_coeff.mpr (congrFun rfl)
  rw[this] at aux
  apply aux

def sturmSeq_CPolynomial (f g : CPolynomial ℚ) : List (CPolynomial ℚ) :=
  if f = 0 then
    []
  else
    f::(sturmSeq_CPolynomial g (-f%g))
termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
  decreasing_by
    if g1: g = 0 then
      simp_all
    else if h : f%g = 0 then
      simp_all
      have : ¬ g.toPoly = 0 := by
        intro hgp
        have : g = 0 := by
          apply CPolynomial.eq_zero_iff_coeff_zero.mpr
          have aux (x : ℚ) := CPolynomial.eval_toPoly x g
          rw[hgp] at aux; simp at aux
          simp only [CPolynomial.coeff_toPoly]
          rw[hgp]
          apply Polynomial.coeff_zero
        simp_all
      have : g.toPoly.degree ≥ 0 := zero_le_degree_iff.mpr this
      have gnatdeg : g.degree ≥ 0 := by
        have aux := CPolynomial.degree_toPoly g
        rw [← aux] at this; exact this
      have : -f % g = 0 := by
        have fgtopoly : (f % g).toPoly = 0 := by rw[h]; exact toPoly_zero
        have : ∃ k , f.toPoly = g.toPoly * k := by
          have : (f % g).toPoly = f.toPoly % g.toPoly := by apply fg_mod_eq
          rw[this] at fgtopoly; simp_all only [ge_iff_le, EuclideanDomain.mod_eq_zero]
          exact fgtopoly
        rcases this with ⟨k, hk⟩
        have : (-f % g).toPoly = 0 := by
          have : (-f % g).toPoly = (-f).toPoly % g.toPoly := by apply fg_mod_eq
          rw[this]
          have : (-f).toPoly = -f.toPoly := by exact toPoly_neg f
          rw[this, hk]
          have : -(g.toPoly * k) = g.toPoly*-k := by simp_all only [ge_iff_le, mul_neg]
          rw[this]; expose_names;
          refine CanonicalEuclideanDomain.mul_mod_eq_zero_of_mod_dvd g.toPoly (-k) g.toPoly this_1 ?_
          have : g.toPoly ∣ g.toPoly := by apply dvd_refl
          exact EuclideanDomain.mod_eq_zero.mpr this
        apply gtopolyzeroeq; exact this
      simp_all
      refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
    else
      simp_all only [↓reduceIte]
      have : ¬ -f % g = 0 := by
        have k1 : ¬ (f % g).toPoly = 0 := by apply gneg_imp_gtopoly_neg; simp; exact h
        have : (f % g).toPoly = f.toPoly % g.toPoly := by exact fg_mod_eq f g
        rw[this] at k1
        have k2 : (-f % g).toPoly = (-f).toPoly % g.toPoly := by apply fg_mod_eq
        have k3 : (-f).toPoly = -f.toPoly := by exact toPoly_neg f
        have k4 : ¬ (-f % g).toPoly = 0 := by
          rw[k2, k3]; simp_all only [EuclideanDomain.mod_eq_zero, dvd_neg, not_false_eq_true]
        apply gtopolyzeroeq2; simp; exact k4
      simp_all
      let f' := f.toPoly
      let g' := g.toPoly
      have : (-f.toPoly % g.toPoly).degree < g.toPoly.degree := by
        refine degree_lt_degree ?_; refine natDegree_mod_lt (-f.toPoly) ?_
        have : g.toPoly.natDegree = 0 → g.toPoly ∣ f.toPoly := by
          intro hg
          have : ∃ c : ℚ, Polynomial.C c = g.toPoly := natDegree_eq_zero.mp hg
          rcases this with ⟨c, rf⟩; use Polynomial.C c⁻¹ * (f.toPoly)
          rw[←rf]; ring_nf
          have hds : c ≠ 0 := by
            by_contra
            have : Polynomial.C c = 0 := by
              rw[this]; aesop
            rw[this] at rf
            have : ¬ g.toPoly = 0 := by
              have : g.toPoly ≠ 0 := by apply gneg_imp_gtopoly_neg; simp; exact g1
              simp at this; exact this
            simp_all
          ext x
          simp_all only [ne_eq]
          rw[←rf]
          have : Polynomial.C c * Polynomial.C c⁻¹ = 1 := by
            have : Polynomial.C (c*c⁻¹ ) = Polynomial.C c * Polynomial.C c⁻¹ := by
              apply C_mul
            rw[← this]; simp_all only [ne_eq, not_false_eq_true, mul_inv_cancel₀, map_one]
          rw[this]; aesop
        have : ¬ (g.toPoly ∣ f.toPoly) → ¬ (g.toPoly.natDegree = 0) := by
          contrapose; exact this
        simp; apply this
        by_contra
        have contr1 : f.toPoly % g.toPoly = 0 := by simp_all only [implies_true, not_true_eq_false, IsEmpty.forall_iff, EuclideanDomain.mod_eq_zero]
        have : ¬ (f % g).toPoly = 0 := by apply gneg_imp_gtopoly_neg; simp; exact h
        have contr2 : (f % g).toPoly = f.toPoly % g.toPoly := by apply fg_mod_eq
        simp_all
      have : (-f % g).toPoly.degree < g.toPoly.degree := by
        have : (-f % g).toPoly = (-f).toPoly % g.toPoly := by apply fg_mod_eq
        rw[this]
        have : (-f).toPoly = -f.toPoly := by exact toPoly_neg f
        rw[this]; simp_all
      have : (-f % g).degree < g.degree := by
        have : (-f%g).degree = (-f%g).toPoly.degree := by exact degree_toPoly (-f%g)
        rw[this]
        have : g.degree = g.toPoly.degree := by exact degree_toPoly g
        rw[this]; simp_all
      refine WithBot.add_lt_add_left ?_ this; intro h; cases h

def seqEval_CPolynomial (k : ℚ) : List (CPolynomial ℚ) → List ℚ
| [] => []
| a::as => (a.eval k)::(seqEval_CPolynomial k as)

noncomputable def seqVar_ab_CPolynomial (P: List (CPolynomial ℚ)) (a b: ℚ): ℤ :=
  (seqVarR (seqEval_CPolynomial a P) : Int) - seqVarR (seqEval_CPolynomial b P)

noncomputable def seqVarSturm_ab_CPolynomial (p q: (CPolynomial ℚ)) (a b : ℚ) : ℤ :=
  seqVar_ab_CPolynomial (sturmSeq_CPolynomial p q) a b

noncomputable def sturmSeq_Rat (f g : Polynomial ℚ) : List (Polynomial ℚ) :=
  if f = 0 then
    []
  else
    f::(sturmSeq_Rat g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
  decreasing_by
    if g1: g = 0 then
      simp_all
    else if h : g ∣ f then
      simp_all
      have gnatdeg : g.degree ≥ 0 := zero_le_degree_iff.mpr g1
      refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
    else
      simp_all only [↓reduceIte, EuclideanDomain.mod_eq_zero, dvd_neg]
      have : (-f % g).degree < g.degree := by
        refine degree_lt_degree ?_; refine natDegree_mod_lt (-f) ?_
        have : g.natDegree = 0 → g ∣ f := by
          intro hg
          have : ∃ c : ℚ, Polynomial.C c = g := natDegree_eq_zero.mp hg
          rcases this with ⟨c, rfl⟩; use Polynomial.C c⁻¹ * f
          have hds : c ≠ 0 := by
            intro abs; rw [abs] at hg; simp at g1; exact g1 abs
          ext x
          simp_all only [map_eq_zero, not_false_eq_true, isUnit_map_iff, isUnit_iff_ne_zero, ne_eq,
            IsUnit.dvd, not_true_eq_false]
        have : g.natDegree ≠ 0 := by simp_all only [imp_false, ne_eq, not_false_eq_true]
        exact this
      refine WithBot.add_lt_add_left ?_ this; simp_all

def seqEval_Rat (k : ℚ) : List (Polynomial ℚ) → List ℚ
| [] => []
| a::as => (eval k a)::(seqEval_Rat k as)

noncomputable def seqVar_ab_Rat (P: List (Polynomial ℚ)) (a b: ℚ): ℤ :=
  (seqVarR (seqEval_Rat a P) : Int) - seqVarR (seqEval_Rat b P)

noncomputable def seqVarSturm_ab_Rat (p q: (Polynomial ℚ)) (a b : ℚ) : ℤ :=
  seqVar_ab_Rat (sturmSeq_Rat p q) a b

/- noncomputable def toPolyList : List (CPolynomial ℚ) → List (Polynomial ℚ) -/
/- | [] => [] -/
/- | a::as => a.toPoly::(toPolyList as) -/

/- theorem seq_eval_equiv (k : ℚ) (c : List (CPolynomial ℚ)) : (seqEval_CPolynomial k c) = (seqEval_Rat k (toPolyList c)) := by sorry -/
/- theorem sturm_seq_equiv (f g : CPolynomial ℚ) : sturmSeq_Rat f.toPoly g.toPoly = toPolyList (sturmSeq_CPolynomial f g) := by sorry -/
/- theorem derivative_equiv (p q : CPolynomial ℚ) : Polynomial.derivative p.toPoly * q.toPoly = (p*q).derivative.toPoly := by sorry -/


-- queremos mostrar que seqVarSturm_ab p (derivative p * q) a b = mesma coisa, mas pros nossos polinomios
theorem equiv_for_sturm_tarski_interval (a b : ℚ) (p q : CPolynomial ℚ) (hab : a < b) (hpa : p.eval a ≠ 0) (hpb : p.eval b ≠ 0) :
    seqVarSturm_ab_CPolynomial p (CPolynomial.derivative (p * q)) a b = seqVarSturm_ab_Rat p.toPoly (derivative p.toPoly * q.toPoly) a b := by
  --simp_all
  rw[seqVarSturm_ab_CPolynomial, seqVar_ab_CPolynomial, seqEval_CPolynomial.eq_def, sturmSeq_CPolynomial]--
  rw[seqVarSturm_ab_Rat, sturmSeq_Rat, seqVar_ab_Rat, seqEval_Rat.eq_def]

  have (a b : ℚ) : (sturmSeq_CPolynomial p (p * q).derivative).length = ((sturmSeq_Rat p.toPoly (p.toPoly * q.toPoly).derivative)).length := by sorry
  if h : p = 0 then
    have : p.toPoly = 0 := by rw[h]; apply toPoly_zero
    simp_all
    rw[seqEval_CPolynomial, seqEval_Rat]
  else
    have : ¬ p.toPoly = 0 := by sorry
    simp_all
    have : CPolynomial.eval a p = Polynomial.eval a p.toPoly := by sorry
    simp_all
    sorry
  --induction on sturmSeq_CPolynomial (p * q).derivative (-p % (p * q).derivative.size se precisar

noncomputable def rootsAbove (f : Polynomial ℝ) (a : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x > a)

noncomputable def tarskiQuery_above (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  ∑ x ∈ rootsAbove p a, sgn (q.eval x)

noncomputable def rootsBelow (f : Polynomial ℝ) (b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x < b)

noncomputable def tarskiQuery_below (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  ∑ x ∈ rootsBelow p b, sgn (q.eval x)

noncomputable def tarskiQuery_R (p q : Polynomial ℝ) : ℤ :=
  ∑ x ∈ p.roots.toFinset, sgn (q.eval x)

lemma seq_sgn_pos_inf_seqEvalSgn (ub : ℝ) (ps : List (Polynomial ℝ)) (key : ∀ x ≥ ub, ∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp) :
    seq_sgn_pos_inf ps = seqEvalSgn ub ps := by
  cases ps
  next => simp only [seq_sgn_pos_inf, seqEvalSgn, List.map]
  next hd tl =>
    simp only [seq_sgn_pos_inf, seqEvalSgn, List.cons.injEq, List.map]
    constructor
    · apply Eq.symm
      apply key
      · exact Preorder.le_refl ub
      · exact List.mem_cons_self
    · apply seq_sgn_pos_inf_seqEvalSgn ub tl
      intros x hx pp hpp
      apply key
      · exact hx
      · exact List.mem_cons_of_mem hd hpp

theorem sturm_tarski_above (a : ℝ) (p q : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    tarskiQuery_above p q a = seqVarAboveSturm p (derivative p * q) a := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p a hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
      a < ub ∧
      (∀ x, x ≥ ub → (∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp)) := by
    apply root_list_ub
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_above p q a = tarskiQuery p q a ub := by
    simp only [tarskiQuery_above, tarskiQuery]
    congr
    simp only [rootsAbove, rootsInInterval]
    ext z
    simp only [gt_iff_lt, Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Set.mem_Ioo, and_congr_right_iff, iff_self_and, and_imp]
    intro a_1 a_2 a_3
    simp_all only [ne_eq, not_false_eq_true, ge_iff_le, ps]
    apply hub1
    on_goal 2 => { exact a_2 }
    · simp_all only
  have changes_changes : seqVarAboveSturm p (derivative p * q) a = seqVarSturm_ab p (derivative p * q) a ub := by
    simp [seqVarSturm_ab, seqVarAboveSturm, seqVarAbove_a, seqVar_ab]
    rw [seqVarSgn, <- ps_def, seq_sgn_pos_inf_seqEvalSgn ub ps hub3]
    rw [seqVarI_seqVarR]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hub2 hpa
  intro abs
  have := hub1 p this ub abs
  simp at this

lemma seq_sgn_neg_inf_seqEvalSgn (lb : ℝ) (ps : List (Polynomial ℝ)) (key : ∀ x ≤ lb, ∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp) :
    seq_sgn_neg_inf ps = seqEvalSgn lb ps := by
  cases ps
  next => simp only [seq_sgn_neg_inf, seqEvalSgn, List.map]
  next hd tl =>
    simp only [seq_sgn_neg_inf, seqEvalSgn, List.cons.injEq, List.map]
    constructor
    · apply Eq.symm
      exact key _ (Preorder.le_refl lb) _ List.mem_cons_self
    · apply seq_sgn_neg_inf_seqEvalSgn lb tl
      intros x hx pp hpp
      exact key _ hx _ (List.mem_cons_of_mem hd hpp)

theorem sturm_tarski_below (b : ℝ) (p q : Polynomial ℝ) (hpa : eval b p ≠ 0) :
    tarskiQuery_below p q b = seqVarBelowSturm p (derivative p * q) b := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p b hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
      b > lb ∧
      (∀ x, x ≤ lb → (∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp)) := by
    apply root_list_lb
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_below p q b = tarskiQuery p q lb b := by
    simp [tarskiQuery_below, tarskiQuery]
    congr
    simp [rootsBelow, rootsInInterval]
    ext z
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      and_congr_right_iff, iff_and_self, and_imp]
    intro a a_1 a_2
    simp_all only [ne_eq, not_false_eq_true, gt_iff_lt, ps]
    apply hlb1
    on_goal 2 => { exact a_1 }
    simp_all only
  have changes_changes : seqVarBelowSturm p (derivative p * q) b = seqVarSturm_ab p (derivative p * q) lb b := by
    simp [seqVarSturm_ab, seqVarBelowSturm, seqVarBelow_b, seqVar_ab]
    rw [seqVarSgn, <- ps_def, seq_sgn_neg_inf_seqEvalSgn lb ps hlb3]
    rw [seqVarI_seqVarR]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hlb2 _ hpa
  intro abs
  have := hlb1 p this lb abs
  simp at this

theorem sturm_tarski_R (p q : Polynomial ℝ) :
    tarskiQuery_R p q = seqVarLineSturm p (derivative p * q) := by
  if hp: p = 0 then
    rw [hp]
    simp [tarskiQuery_R, seqVarLineSturm, seqVarLine, seq_sgn_neg_inf, seq_sgn_pos_inf]
  else
    let ps := sturmSeq p (derivative p * q)
    have ps_def : ps = sturmSeq p (derivative p * q) := rfl
    have : p ∈ ps := by
      unfold ps sturmSeq
      simp [hp]
    obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
        0 > lb ∧
        (∀ x, x ≤ lb → (∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp)) := by
      apply root_list_lb
      exact no_zero_in_sturmSeq p (derivative p * q)
    obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
        0 < ub ∧
        (∀ x, x ≥ ub → (∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp)) := by
      apply root_list_ub
      exact no_zero_in_sturmSeq p (derivative p * q)
    have taq_taq : tarskiQuery_R p q = tarskiQuery p q lb ub := by
      simp [tarskiQuery_R, tarskiQuery]
      congr
      unfold rootsInInterval
      ext z
      simp only [Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def, Set.mem_Ioo,
        Finset.mem_filter, iff_self_and, and_imp]
      intro a a_1
      simp_all only [not_false_eq_true, gt_iff_lt, ge_iff_le, ps]
      apply And.intro
      · apply hlb1
        on_goal 2 => { exact a_1 }
        · simp_all only
      · apply hub1
        · exact this
        · simp_all only
    have changes_changes : seqVarLineSturm p (derivative p * q) = seqVarSturm_ab p (derivative p * q) lb ub := by
      simp [seqVarLineSturm, seqVarLine, seqVarSturm_ab, seqVar_ab]
      rw [ seqVarSgn
         , seqVarSgn
         , <- ps_def
         , seq_sgn_neg_inf_seqEvalSgn lb ps hlb3
         , seq_sgn_pos_inf_seqEvalSgn ub ps hub3
         , seqVarI_seqVarR
         , seqVarI_seqVarR
         ]
    have lb_neq_0 : eval lb p ≠ 0 := by
      intro abs
      have := hlb1 p this lb abs
      simp at this
    have ub_neq_0 : eval ub p ≠ 0 := by
      intro abs
      have := hub1 p this ub abs
      simp at this
    have lb_ub : lb < ub := by linarith
    rw [taq_taq, changes_changes]
    exact sturm_tarski_interval lb ub p q lb_ub lb_neq_0 ub_neq_0

theorem sturm_interval (a b : ℝ) (p : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    Finset.card (rootsInInterval p a b) = seqVarSturm_ab p (derivative p) a b := by
  have := sturm_tarski_interval a b p 1 hab hpa hpb
  simp [tarskiQuery, sgn] at this
  exact this

theorem sturm_above (a : ℝ) (p : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    Finset.card (rootsAbove p a) = seqVarAboveSturm p (derivative p) a := by
  have := sturm_tarski_above a p 1 hpa
  simp [tarskiQuery_above, sgn] at this
  exact this

theorem sturm_below (b : ℝ) (p : Polynomial ℝ) (hpa : eval b p ≠ 0) :
    Finset.card (rootsBelow p b) = seqVarBelowSturm p (derivative p) b := by
  have := sturm_tarski_below b p 1 hpa
  simp [tarskiQuery_below, sgn] at this
  exact this

theorem sturm_R (p : Polynomial ℝ) :
    Finset.card p.roots.toFinset = seqVarLineSturm p (derivative p) := by
  have := sturm_tarski_R p 1
  simp [tarskiQuery_R, sgn] at this
  exact this

end Theorem
