import Mathlib

import Smt.Reconstruct.Real.CAD.Sturm.CauchyIndex

open Polynomial Set Filter Classical

noncomputable section

lemma no_zero_in_sturmSeq (p q : Polynomial ℝ) : 0 ∉ sturmSeq p q := by
  induction' H: sturmSeq p q generalizing p q
  next => simp
  next hd tl IH =>
    unfold sturmSeq at H
    have : p :: sturmSeq q (-p % q) = hd :: tl := by aesop
    simp
    constructor
    · simp_all only [ite_eq_right_iff, List.nil_eq, reduceCtorEq, imp_false, List.cons.injEq]
      obtain ⟨left, right⟩ := this
      subst left right
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_true_eq_false]
    · have : sturmSeq q (-p % q) = tl := List.tail_eq_of_cons_eq this
      apply IH q (-p % q)
      exact this

lemma seqVarSgn : ∀ ps : List (Polynomial ℝ), ∀ (k : ℝ), seqVarR (seqEval k ps) = seqVarR (seqEvalSgn k ps)
| [] => by intro k; simp [seqVarR, seqEval, seqEvalSgn]
| [p] => by intro k; simp [seqVarR, seqEval, seqEvalSgn]
| p1 :: p2 :: ps => by
  intro k
  simp [seqVarR, seqEval, seqEvalSgn]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact seqVarSgn (p1 :: ps) k
  · have := (sgn_sgn_zero (eval k p2)).mpr h1
    exact False.elim (h2 this)
  · rw [h1] at h2
    simp only [sgn, gt_iff_lt, lt_self_iff_false, ↓reduceIte, not_true_eq_false] at h2
  · unfold sgn at h5
    split_ifs at h5
    simp only [one_ne_zero] at h5
  · simp only [add_right_inj]
    exact seqVarSgn (p2 :: ps) k
  · push_neg at h6
    by_cases eval k p2 < 0
    next H =>
      have : eval k p1 > 0 := (pos_iff_neg_of_mul_neg h4).mpr H
      have s1 : 0 < sgn (eval k p1) := (sgn_sgn_pos (eval k p1)).mpr this
      have s2 : 0 > sgn (eval k p2) := (sgn_sgn_neg (eval k p2)).mpr H
      have : sgn (eval k p1) * sgn (eval k p2) < 0 := Int.mul_neg_of_pos_of_neg s1 s2
      norm_cast at h6
      linarith
    next H =>
      push_neg at H
      exfalso
      have : 0 < eval k p2 := lt_of_le_of_ne H fun a => h1 (Eq.symm a)
      have s1 : 0 < sgn (eval k p2) := (sgn_sgn_pos (eval k p2)).mpr this
      have : eval k p1 < 0 := neg_of_mul_neg_left h4 H
      have s2 : sgn (eval k p1) < 0 := (sgn_sgn_neg (eval k p1)).mpr this
      have : sgn (eval k p1) * sgn (eval k p2) < 0 := Int.mul_neg_of_neg_of_pos s2 s1
      norm_cast at h6
      linarith
  · have := (sgn_sgn_zero (eval k p2)).mp h7
    exact False.elim (h1 this)
  · push_neg at h4
    by_cases eval k p2 < 0
    next H =>
      have : eval k p1 ≤ 0 := nonpos_of_mul_nonneg_left h4 H
      cases Decidable.lt_or_eq_of_le this
      next H1 =>
        have s1 : sgn (eval k p2) < 0 := (sgn_sgn_neg (eval k p2)).mpr H
        have s2 : sgn (eval k p1) < 0 := (sgn_sgn_neg (eval k p1)).mpr H1
        have : sgn (eval k p1) * sgn (eval k p2) > 0 := Int.mul_pos_of_neg_of_neg s2 s1
        norm_cast at h8
        linarith
      next H1 =>
        have : sgn (eval k p1) = 0 := (sgn_sgn_zero (eval k p1)).mpr H1
        rw [this] at h8
        simp at h8
    next H =>
      push_neg at H
      have H : 0 < eval k p2 := lt_of_le_of_ne H fun a => h1 (Eq.symm a)
      have : 0 ≤ eval k p1 := (mul_nonneg_iff_of_pos_right H).mp h4
      cases Decidable.lt_or_eq_of_le this
      next H1 =>
        have s1 : sgn (eval k p1) > 0 := (sgn_sgn_pos (eval k p1)).mpr H1
        have s2 : sgn (eval k p2) > 0 := (sgn_sgn_pos (eval k p2)).mpr H
        have : sgn (eval k p1) * sgn (eval k p2) > 0 := Int.mul_pos s1 s2
        norm_cast at h8
        linarith
      next H1 =>
        have : sgn (eval k p1) = 0 := (sgn_sgn_zero (eval k p1)).mpr H1.symm
        rw [this] at h8
        simp at h8
  · exact seqVarSgn (p2 :: ps) k

lemma smod_nil_eq (p q : Polynomial Real) :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    by_contra!
    unfold sturmSeq at hs
    simp [this] at hs
  · intro hp
    simp [hp, sturmSeq]

@[simp]
lemma smods_s_0_1 (p: Polynomial ℝ) : sturmSeq 0 p = [] := (smod_nil_eq 0 p).mpr rfl

@[simp]
lemma smods_s_0_2 (p: Polynomial ℝ) : sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with H
  · exact (smod_nil_eq p 0).mpr H
  · unfold sturmSeq; simp [H]

@[simp]
theorem seqVarSturm_ab_z_1 (p: Polynomial ℝ) (a b: ℝ) : seqVarSturm_ab 0 p a b = 0 := by
  unfold seqVarSturm_ab seqVar_ab seqVarR seqEval sturmSeq
  simp

@[simp]
theorem seqVarSturm_ab_z_2 (p: Polynomial ℝ) (a b: ℝ) : seqVarSturm_ab p 0 a b = 0 := by
  unfold seqVarSturm_ab seqVar_ab seqVarR seqEval
  if H: p = 0 then simp [H]
  else simp [H]

lemma cauchyIndex_poly_taq (p q : Polynomial ℝ) (a b : ℝ) :
    tarskiQuery p q a b = cauchyIndex p (derivative p * q) a b := by
  if hp : p = 0 then
    simp_rw [hp, tarskiQuery, cauchyIndex, rootsInIntervalZero]
    norm_num
  else
    unfold tarskiQuery cauchyIndex
    apply Finset.sum_congr rfl
    intros x hx
    have : p.eval x = 0 := by
      simp [rootsInInterval] at hx
      exact hx.1.2
    rw [jump_poly_sign p q x hp this]

theorem changes_itv_smods_rec {a b: ℝ} {p q: Polynomial ℝ} (hpqa: eval a (p * q)≠ 0) (hpqb: eval b (p * q) ≠ 0) :
    (seqVarSturm_ab p q a b) = cross (p * q) a b + seqVarSturm_ab q (-p%q) a b := by
  if H: p = 0 ∨ q = 0 ∨ p % q = 0 then
    rcases H with h | h | h
    · simp [cross, variation, h]
    · simp [cross, variation, h]
    · unfold seqVarSturm_ab seqVar_ab seqEval cross seqVarR sturmSeq
      rw [mod_minus, h]
      have ⟨hap, haq⟩: eval a p ≠ 0 ∧ eval a q ≠ 0 := by simp_all only [eval_mul, ne_eq, mul_eq_zero, not_or,
        EuclideanDomain.mod_eq_zero, not_false_eq_true, and_self]
      have ⟨hbp, hbq⟩: eval b p ≠ 0 ∧ eval b q ≠ 0:= by simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self,
        not_false_eq_true, not_or, EuclideanDomain.mod_eq_zero, and_self]
      have hpz: p ≠ 0 := by
        simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self, not_false_eq_true, EuclideanDomain.mod_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [dvd_zero, eval_zero, not_true_eq_false]
      have hqz: q ≠ 0 := by
        simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self, not_false_eq_true, EuclideanDomain.mod_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [zero_dvd_iff]
      simp [hpz, hqz, haq, hbq]
      split_ifs with h1 h2 h3
      · unfold seqVarR
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.2 ⟨h1, h2⟩];
        simp
      · unfold seqVarR
        have : eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqb
          rw [not_lt, <-ge_iff_le] at h2
          exact lt_of_le_of_ne h2 (Ne.symm hpqb)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.1 ⟨h1, this⟩];
        simp
      · unfold seqVarR
        have : eval a p * eval a q > 0 := by
          rw [eval_mul] at hpqa
          rw [not_lt, <-ge_iff_le] at h1
          exact lt_of_le_of_ne h1 (Ne.symm hpqa)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.1 ⟨this, h3⟩];
        simp
      · unfold seqVarR
        have : eval a p * eval a q > 0 ∧ eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqa hpqb
          rw [not_lt, <-ge_iff_le] at h1 h3
          exact ⟨lt_of_le_of_ne h1 (Ne.symm hpqa), lt_of_le_of_ne h3 (Ne.symm hpqb)⟩
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).1 this];
        simp
   else
     simp only [not_or] at H
     have ⟨ps, httl, htlmod⟩ : ∃ ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: -p%q:: ps ∧ sturmSeq q (-p%q) = q :: (-p%q) :: ps := by
       unfold sturmSeq sturmSeq
       rw [sturmSeq]
       simp_all
     let changes_diff := fun x => ((seqVarR (seqEval x (p::q::(-p%q)::ps)): ℤ) - (seqVarR (seqEval x (q::(-p%q)::ps))): ℤ)
     have hz1: ∀ x: ℝ, (eval x p) * (eval x q) < 0 → changes_diff x = 1 := by
       unfold changes_diff
       intros x hx
       rw [seqVarR.eq_def, seqEval]
       have hxq : eval x q ≠ 0 := by
         simp_all only [eval_mul, ne_eq, mul_eq_zero, not_or, EuclideanDomain.mod_eq_zero]
         obtain ⟨left, right⟩ := hpqa
         obtain ⟨left_1, right_1⟩ := hpqb
         obtain ⟨left_2, right_2⟩ := H
         obtain ⟨left_3, right_2⟩ := right_2
         apply Aesop.BuiltinRules.not_intro
         intro a_1
         simp_all only [mul_zero, lt_self_iff_false]
       simp [hxq, hx]
     have hz2: ∀x, (eval x p) * (eval x q) > 0 → changes_diff x = 0 := by
       unfold changes_diff
       intros x hx
       rw [seqVarR.eq_def, seqEval]
       have hxq : eval x q ≠ 0 := by
         simp_all only [eval_mul, ne_eq, mul_eq_zero, not_or, EuclideanDomain.mod_eq_zero, gt_iff_lt, changes_diff]
         obtain ⟨left, right⟩ := hpqa
         obtain ⟨left_1, right_1⟩ := hpqb
         obtain ⟨left_2, right_2⟩ := H
         obtain ⟨left_3, right_2⟩ := right_2
         apply Aesop.BuiltinRules.not_intro
         intro a_1
         simp_all only [mul_zero, lt_self_iff_false]
       have  : ¬ eval x p * eval x q < 0 := by nlinarith
       simp [hxq, this]
     have hf: changes_diff a - changes_diff b = cross (p * q) a b := by
       unfold cross
       rcases lt_or_gt_of_ne hpqa with ha | ha <;> rcases lt_or_gt_of_ne hpqb with hb | hb
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.2.2 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.2.1 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.1 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).1 ⟨ha, hb⟩]
         simp_all
     unfold changes_diff at hf
     unfold seqVarSturm_ab
     rw [httl, htlmod, ← sub_eq_iff_eq_add]
     unfold seqVar_ab
     ring_nf at hf ⊢
     rw [hf]

theorem cauchyIndex_sturmSeq_aux (p q: Polynomial ℝ) (a b: ℝ) (hab: a < b): ∃ (a' b': ℝ), a < a' ∧ a' < b' ∧ b' < b ∧ (∀p' ∈ sturmSeq p q, (∀ x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by
  induction h: (sturmSeq p q) generalizing p q with
    | nil =>
      let a' := 2/3 * a + 1/3 * b
      let b' := 1/3 * a + 2/3 * b
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by
        repeat' constructor
        · unfold a'; linarith
        · unfold a' b'; linarith
        · unfold b'; linarith
      have hn_root:(∀p' ∈ [], ∀ x:ℝ, (((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → (eval x p' ≠ 0))) := by simp
      use a', b'
    | cons hd tl ih =>
      let r := - (p % q)
      have hpz: p ≠ 0 := by
        simp_all only [ne_eq, exists_and_left]
        intro a_1
        subst a_1
        simp_all only [smods_s_0_1, List.nil_eq, reduceCtorEq]
      have htl: sturmSeq q r = tl := by
        unfold sturmSeq at h;
        simp [hpz] at h
        unfold r
        rw [<-mod_minus]; exact h.2
      have h_concat: sturmSeq p q = p :: tl := by
        unfold sturmSeq at h ⊢; simp [hpz] at h; simp [h.2, hpz]
      have h_hd: hd = p := by
        subst htl
        simp_all only [ne_eq, exists_and_left, List.cons.injEq, and_true, r]
      have ⟨a1, b1, haa1, ha1b1, hbb1, ha1b1_nroot⟩: ∃ (a1 b1: ℝ), a < a1 ∧ a1 < b1 ∧ b1 < b ∧
           (∀p' ∈ tl, (∀ x: ℝ, ((a < x ∧ x ≤ a1) ∨ (b1 ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by
        exact ih q r htl
      have ⟨a2, b2, haa2, ha2_nroot, hbb2, hb2_nroot⟩ : ∃ (a2 b2: ℝ), a < a2 ∧ (∀x: ℝ, (a < x ∧ x ≤ a2) -> eval x p ≠ 0) ∧
                                                         (b2 < b) ∧ (∀x: ℝ, (b2 ≤ x ∧ x < b) -> eval x p ≠ 0) := by
        have ⟨a2, haa2, ha2_nroot⟩ := next_non_root_interval p a hpz
        have ⟨b2, hbb2, hb2_nroot⟩ := last_non_root_interval p b hpz
        use a2, b2
        simp_all
      let a' := if b2 > a then min a1 (min b2 a2) else min a1 a2
      let b' := if a2 < b then max b1 (max a2 b2) else max b1 b2
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by
        unfold a' b'
        constructor <;> split_ifs <;> simp_all
      have h_rec: ∀p' ∈ tl, ∀x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b))  -> eval x p' ≠ 0 := by
        have ha'a1: a' ≤ a1 := by unfold a'; split_ifs <;> simp
        have hb'b: b1 ≤ b' := by unfold b'; split_ifs <;> simp
        intros p' haux x hx
        rcases hx with hl | hr
        · have : a < x ∧ x ≤ a1 := by constructor <;> linarith
          exact ha1b1_nroot p' haux x (Or.inl this)
        · have : b1 ≤ x ∧ x < b := by constructor <;> linarith
          exact ha1b1_nroot p' haux x (Or.inr this)
      have h_final: ∀ x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) -> eval x p ≠ 0 := by
        unfold a' b'; intros x
        split_ifs <;> intros hx <;> simp only [le_inf_iff, sup_le_iff] at hx
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2, hr.2⟩
      use a', b'
      rw [h_hd]
      simp [haa', ha'b', hbb']
      exact ⟨h_final, h_rec⟩

lemma cauchyIndex_poly_rec (p q : Polynomial ℝ) (a b: ℝ) (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    cauchyIndex p q a b = cross (p * q) a b + cauchyIndex q (- p % q) a b
    := by
  have H := cindex_poly_inverse_add_cross p q a b hab ha hb
  have : - cauchyIndex q p a b = cauchyIndex q (- p % q) a b := by
    have h1 := cauchyIndex_poly_mod q (-p) a b
    have h2 := cauchyIndex_smult_1 q p a b (-1)
    simp [sgn] at h2
    have : (if (1 : Real) < 0 then cauchyIndex q p a b else (-cauchyIndex q p a b)) = -cauchyIndex q p a b := by
      split
      next h => linarith
      next h => rfl
    rw [this] at h2
    clear this
    rw [<- h2, h1]
  simp only [cross, variation] at *
  linarith

lemma changes_smods_congr (p q : Polynomial ℝ) (a a' : ℝ) (haa' : a ≠ a') (hpa : eval a p ≠ 0)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (a' ≤ x ∧ x < a)) → eval x p' ≠ 0) :
    seqVarR (seqEval a (sturmSeq p q)) = seqVarR (seqEval a' (sturmSeq p q)) := by
  have p_neq_0 : p ≠ 0 := eval_non_zero p a hpa
  let r1 := -p%q
  have r1_def : r1 = -p%q := rfl
  have a_a'_rel: ∀ pp ∈ sturmSeq p q, eval a pp * eval a' pp ≥ 0 := by
    by_contra!
    obtain ⟨pp, hpp1, hpp2⟩ := this
    if haa': a < a' then
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : ℝ, a < x ∧ x < a' ∧ eval x pp = 0 := exists_root_ioo_mul (le_of_lt haa') hpp2
      have := no_root pp hpp1 x (Or.inl (And.intro hx1 (le_of_lt hx2)))
      exact this hx3
    else
      simp at haa'
      rw [mul_comm] at hpp2
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : ℝ, a' < x ∧ x < a ∧ eval x pp = 0 := exists_root_ioo_mul haa' hpp2
      have := no_root pp hpp1 x (Or.inr (And.intro (le_of_lt hx1) hx2))
      exact this hx3

  if hq: q = 0 then
    unfold sturmSeq
    simp [hq, seqEval, seqVarR, p_neq_0]
  else if hq2: eval a q = 0 then
    let r2 := -(q%r1)
    have : eval a p = - (eval a r1) := by
      have h1 := EuclideanDomain.quotient_mul_add_remainder_eq p q
      have h2 : r1 = EuclideanDomain.remainder (-p) q := by rfl
      have : eval a p = eval a (q * EuclideanDomain.quotient p q + EuclideanDomain.remainder p q) := by
        congr
        exact (Eq.symm h1)
      rw [this]
      simp [hq2]
      rw [h2]
      have : ∀ p q : Polynomial ℝ, EuclideanDomain.remainder p q = p % q := by intros p q; rfl
      rw [this, this (-p) q, mod_minus]
      simp
    have : eval a r1 = -eval a p := by linarith
    have h_eval_r : eval a r1 ≠ 0 := by rw [this]; exact neg_ne_zero.mpr hpa
    have r_neq_0 : r1 ≠ 0 := eval_non_zero r1 a h_eval_r
    have eval_a_eval_r : eval a p * eval a r1 < 0 := by rw [this]; simp; exact hpa
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: r1 :: ps ∧ sturmSeq r1 r2 = r1 :: ps := by
      unfold sturmSeq
      simp [p_neq_0, r_neq_0]
      rw [<- r1_def]
      nth_rw 1 [sturmSeq]
      simp [hq]
      nth_rw 1 [sturmSeq]
      split_ifs
      next h => exact r_neq_0 h
      next h =>
        congr <;> exact mod_minus q r1
    have : List.length (sturmSeq r1 r2) < List.length (sturmSeq p q) := by simp [hps1, hps2]
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq r1 r2, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: r1 :: ps := by
        simp
        right
        right
        simp at hp'
        exact hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr r1 r2 a a' haa' h_eval_r no_root_2
    have rec_a : seqVarR (seqEval a (sturmSeq p q)) = 1 + seqVarR (seqEval a (sturmSeq r1 r2)) := by
      rw [hps1, hps2, seqEval]
      simp [seqVarR, hq2]
      simp [h_eval_r]
      exact eval_a_eval_r
    have rec_a' : seqVarR (seqEval a' (sturmSeq p q)) = 1 + seqVarR (seqEval a' (sturmSeq r1 r2)) := by
      have hp1 : eval a p * eval a' p ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        exact List.mem_cons_self
      have hr1 : eval a r1 * eval a' r1 ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        simp only [List.mem_cons, true_or, or_true]
      have ev_neq_0_p : eval a' p ≠ 0 := by
        rw [hps1] at no_root
        apply no_root p List.mem_cons_self
        aesop
      have ev_neq_0_r1 : eval a' r1 ≠ 0 := by
        rw [hps1] at no_root
        apply no_root r1
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      have ev_neq_0_q : eval a' q ≠ 0 := by
        rw [hps1] at no_root
        apply no_root q
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      rw [hps1, hps2]
      rw [seqEval, List.map, List.map]
      rw [seqVarR]
      simp [ev_neq_0_q]
      split_ifs
      next H =>
        simp [seqVarR, ev_neq_0_r1]
        by_contra!
        have : (eval a' p * eval a' q) * (eval a' q * eval a' r1) > 0 := mul_pos_of_neg_of_neg H this
        have h1 : (eval a' p * eval a' r1) * (eval a' q * eval a' q) > 0 := by linarith
        have h2 : eval a' q * eval a' q > 0 := mul_self_pos.mpr ev_neq_0_q
        have h_pos : eval a' p * eval a' r1 > 0 := (pos_iff_pos_of_mul_pos h1).mpr h2
        have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1
        have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith
        have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right h_pos).mp this
        linarith
      next H =>
        simp [seqVarR, ev_neq_0_r1]
        simp at H
        by_contra!
        have : 0 ≤ (eval a' p * eval a' q) * (eval a' q * eval a' r1) := Left.mul_nonneg H this
        have h1 : 0 ≤ (eval a' p * eval a' r1) * (eval a' q * eval a' q) := by linarith
        have h2 : 0 < eval a' q * eval a' q := mul_self_pos.mpr ev_neq_0_q
        have h_pos : 0 ≤ eval a' p * eval a' r1 := (mul_nonneg_iff_of_pos_right h2).mp h1
        have ev_pos : 0 < eval a' p * eval a' r1 := by
          by_contra!
          have : 0 = eval a' p * eval a' r1 := by linarith
          have : eval a' p = 0 ∨ eval a' r1 = 0 := mul_eq_zero.mp (id (Eq.symm this))
          cases this
          next inl => exact ev_neq_0_p inl
          next inr => exact ev_neq_0_r1 inr
        have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1
        have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith
        have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right ev_pos).mp this
        linarith
    rw [rec_a, rec_a', IH]
  else
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: ps ∧ sturmSeq q r1 = q :: ps := by
      rw [sturmSeq]
      simp [p_neq_0]
      rw [sturmSeq]
      simp [hq]
    have : List.length (sturmSeq q r1) < List.length (sturmSeq p q) := by
      rw [hps1, hps2]
      simp
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq q r1, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: ps := List.mem_cons_of_mem p hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr q r1 a a' haa' hq2 no_root_2
    have hpa' : eval a' p ≠ 0 := by
      apply no_root p (by rw [hps1]; exact List.mem_cons_self)
      aesop
    have hqa' : eval a' q ≠ 0 := by
      apply no_root q (by rw [hps1]; simp)
      aesop
    have ev_pa' : eval a p * eval a' p ≥ 0 := by
      apply a_a'_rel p (by rw [hps1]; exact List.mem_cons_self)
    have ev_qa' : eval a q * eval a' q ≥ 0 := by
      apply a_a'_rel q (by rw [hps1]; simp)
    rw [hps1]
    simp [seqEval, seqVarR, hq2, hqa']
    have eq_a : seqVarR (eval a q :: seqEval a ps) = seqVarR (seqEval a (q :: ps)) := by simp [seqEval]
    have eq_a' : seqVarR (eval a' q :: seqEval a' ps) = seqVarR (seqEval a' (q :: ps)) := by simp [seqEval]
    rw [hps2] at IH
    split_ifs
    next h1 h2 => unfold seqEval at eq_a eq_a' IH; rw [eq_a, eq_a', IH]
    next h1 h2 =>
      push_neg at h2
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      by_cases eval a p > 0
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (Eq.symm a_1)
          have : eval a p * eval a q > 0 := Left.mul_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := lt_of_le_of_ne this (Ne.symm hqa')
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' q * eval a' p < 0 := mul_neg_of_neg_of_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q > 0 := mul_pos_of_neg_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := lt_of_le_of_ne this hqa'
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' p * eval a' q < 0 := mul_neg_of_neg_of_pos Ha'p Ha'q
        linarith
    next h1 h2 =>
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      by_cases eval a p > 0
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := (pos_iff_neg_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' q * eval a' p > 0 := Left.mul_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (id (Eq.symm a_1))
          have : eval a p * eval a q < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := (neg_iff_pos_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' p * eval a' q > 0 := mul_pos_of_neg_of_neg Ha'p Ha'q
        linarith
    next h1 h2 => unfold seqEval at eq_a eq_a' IH; rw [eq_a, eq_a', IH]
termination_by List.length (sturmSeq p q)

lemma changes_itv_smods_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0)
    (haa' : a < a') (hb'b : b' < b)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p' ≠ 0) :
    seqVarSturm_ab p q a b = seqVarSturm_ab p q a' b' := by
  have h1 : seqVarR (seqEval a (sturmSeq p q)) = seqVarR (seqEval a' (sturmSeq p q)) := by
    apply changes_smods_congr p q a a'
    · exact ne_of_lt haa'
    · exact hpa
    · intros p' hp' x hx
      apply no_root p' hp'
      left
      cases hx
      next hx => exact hx
      next hx => linarith
  have h2 : seqVarR (seqEval b (sturmSeq p q)) = seqVarR (seqEval b' (sturmSeq p q)) := by
    apply changes_smods_congr p q b b'
    · exact Ne.symm (ne_of_lt hb'b)
    · exact hpb
    · intros p' hp' x hx
      apply no_root p' hp'
      right
      cases hx
      next hx => linarith
      next hx => exact hx
  unfold seqVarSturm_ab seqVar_ab
  rw [h1, h2]

theorem cauchyIndex_sturmSeq (p q: Polynomial ℝ) (a b : ℝ) (hpa: p.eval a ≠ 0) (hpb : p.eval b ≠ 0) (hab : a < b) :
    seqVarSturm_ab p q a b = cauchyIndex p q a b := by
  induction h: (sturmSeq p q) generalizing p q a b with
  | nil =>
    unfold seqVarSturm_ab
    rw [h]
    simp [seqVar_ab, seqVarR, seqEval]
    have := (smod_nil_eq p q).mp h
    rw [this]
    simp [cauchyIndex, rootsInInterval]
   | cons hd tl ih =>
      have : p ≠ 0 := eval_non_zero p a hpa
      have ⟨a', b', haa', ha'b', hbb', hn_root⟩ := cauchyIndex_sturmSeq_aux p q a b hab
      if H: q = 0 then simp [H]
      else
        let r := (-p % q)
        have ⟨ps, hps, hpsqr, htlps⟩: ∃ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: ps ∧ sturmSeq q r = q :: ps ∧ tl = q :: ps := by
          have ⟨hhd, haux1⟩: p = hd ∧ sturmSeq q (-p % q) = tl := by
            unfold sturmSeq at h
            simp [this] at h
            exact h
          have haux2: q :: sturmSeq (-p % q) (-q % (-p % q)) = tl := by
            unfold sturmSeq at haux1
            simp [H] at haux1
            exact haux1
          use sturmSeq (-p % q) (-q % (-p % q))
          simp [r, haux1, haux2, h]
          exact (Eq.symm hhd)
        have ⟨hpa', hpb', hqa', hqb'⟩ : eval a' p ≠ 0 ∧ eval b' p ≠ 0 ∧  eval a' q ≠ 0 ∧ eval b' q ≠ 0 := by aesop
        have t0 : a' < b' := by linarith
        rw [htlps] at ih
        have h_ind := ih q r a' b' hqa' hqb' t0 hpsqr
        have : (∀ p' ∈ sturmSeq p q, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ b' ≤ x ∧ x < b → eval x p' ≠ 0) :=
          fun p' a_1 x a => hn_root p' a_1 x a
        have h_congr_seqvar := changes_itv_smods_congr p q a a' b b' hpa hpb haa' hbb' this
        rw [h_congr_seqvar]
        have : (∀ (x : ℝ), a < x ∧ x ≤ a' ∨ b' ≤ x ∧ x < b → eval x p ≠ 0) := by
          intro x hx
          rcases hn_root p (by rw [hps]; simp) x hx with hneq
          exact hneq
        have h_congr_cindex := cindex_poly_congr p q a a' b b' haa' hbb' t0 this
        have t1 : eval a' (p * q) ≠ 0 := by simp [Polynomial.eval_mul, hpa', hqa']
        have t2 : eval b' (p * q) ≠ 0 := by simp [Polynomial.eval_mul, hpb', hqb']
        have h_cindex := cauchyIndex_poly_rec p q a' b' ha'b' t1 t2
        have h_changes_itv := changes_itv_smods_rec t1 t2
        rw [h_congr_cindex, h_cindex, h_changes_itv, h_ind]
