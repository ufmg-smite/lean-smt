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

theorem toPoly_ne0_of_poly_ne0 (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
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
