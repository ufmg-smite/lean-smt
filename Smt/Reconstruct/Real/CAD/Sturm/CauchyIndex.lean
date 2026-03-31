import Smt.Reconstruct.Real.CAD.Sturm.JumpPoly
import Mathlib.RingTheory.Polynomial.Content

noncomputable section

open Polynomial

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

def variation (a b : Real) : Int :=
  if a * b ≥ 0 then 0 else if a < b then 1 else -1

def cross (p : Polynomial Real) (a b : Real) : Int :=
  variation (p.eval a) (p.eval b)

lemma cross_no_root {a b: ℝ} {p: Polynomial ℝ} (hab: a < b) (hxnroot: rootsInInterval p a b = ∅) :
      (cross p a b = 0) := by
  have hone : ¬ (eval a p > 0 ∧ eval b p < 0) := by
    by_contra!
    have ⟨r, hr⟩ := exists_root_ioo' (le_of_lt hab) (this.1) (this.2)
    have hr_int: r ∈ rootsInInterval p a b := by unfold rootsInInterval; aesop
    simp_all only [gt_iff_lt, Finset.notMem_empty]
  have htwo: ¬ (eval a p < 0 ∧ eval b p > 0) := by
    by_contra!
    have ⟨r, hr⟩ := exists_root_ioo (le_of_lt hab) (this.1) (this.2)
    have hr_int: r ∈ rootsInInterval p a b := by unfold rootsInInterval; aesop
    simp_all only [gt_iff_lt, not_and, not_lt, Finset.notMem_empty]
  have : (eval a p) * (eval b p) >= 0 := by
    if H: eval a p = 0 then simp [H]
    else
    if H': eval a p >  0 then
      have hbp : eval b p >= 0 := by simp_all
      nlinarith
    else
      have H' : eval a p < 0 := by simp at H'; exact lt_of_le_of_ne H' H
      have hbp : eval b p <= 0 := by simp_all
      nlinarith
  simp [cross, variation, this]

lemma cauchyIndex_poly_mod (p q : Polynomial Real) (a b : Real) :
    cauchyIndex p q a b = cauchyIndex p (q % p) a b := by
  unfold cauchyIndex
  have := jump_poly_mod p q
  exact Finset.sum_congr rfl fun x a => this x

lemma cauchyIndex_smult_1 (p q : Polynomial Real) (a b c : Real) :
    cauchyIndex p (C c * q) a b = sgn c * cauchyIndex p q a b := by
  unfold cauchyIndex
  have : sgn c * ∑ x ∈ rootsInInterval p a b, jump_val p q x = ∑ x ∈ rootsInInterval p a b, sgn c * (jump_val p q x) := Finset.mul_sum (rootsInInterval p a b) (jump_val p q) (sgn c)
  rw [this]
  congr
  ext x
  exact jump_poly_smult_1 p q c x

theorem variation_mult_pos1 (c x y : ℝ) (hc : c > 0) : variation (c*x) y = variation x y := by
  rw [variation, variation]
  have sgnequals : (0 ≤ x*y) = (0 ≤ c*x*y) := by
    simp
    constructor
    · intro hxy
      ring_nf; simp_all
      have : c*x*y = c*(x*y):= by linarith
      simp_all
    · intro hcxy
      ring_nf; simp_all
      have : c * 0 ≤ c * (x * y) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcxy
      simp_all only [mul_zero, mul_nonneg_iff_of_pos_left]
  have hneg : c * x * y < 0 → (c * x < y ↔ x < y) := by
    intro hcy
    simp_all
    have hxy : x * y < 0 := (lt_iff_lt_of_le_iff_le (Iff.symm sgnequals)).mp hcy
    have : (c * x < y) = (x < y) := by
      simp_all
      constructor
      · intro hcxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          exact lt_trans hx0 hy0
        next hy => nlinarith
      · intro hxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          have hcx0 : c * x < 0 := mul_neg_of_pos_of_neg hc hx0
          exact lt_trans hcx0 hy0
        next hy0 => nlinarith
    rw[this]
  have : (if 0 ≤ c * x * y then 0 else if c * x < y then 1 else -1)
     = (if 0 ≤ c * x * y then 0 else if x < y then 1 else -1) := by
    by_cases hcy : 0 ≤ c * x * y
    · simp [hcy]
    · have hcy' : c * x * y < 0 := lt_of_not_ge hcy
      have hx : (c * x < y ↔ x < y) := (hneg hcy')
      simp [hcy, hx]
  simp_all only [gt_iff_lt, eq_iff_iff, ge_iff_le]

theorem variation_mult_pos2 (c x y : ℝ) (hc : c > 0) : variation x (c*y) = variation x y := by
  rw[variation, variation]
  have sgnequals : (0 ≤ x*y) = (0 ≤ c*x*y) := by
    simp
    constructor
    · intro hxy
      ring_nf; simp_all
      have : c*x*y = c*(x*y):= by linarith
      simp_all
    · intro hcxy
      ring_nf; simp_all
      have : c * 0 ≤ c * (x * y) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcxy
      simp_all only [mul_zero, mul_nonneg_iff_of_pos_left]
  have hneg : c * x * y < 0 → (x < c * y ↔ x < y) := by
    intro hcy
    simp_all
    have hxy : x * y < 0 := (lt_iff_lt_of_le_iff_le (Iff.symm sgnequals)).mp hcy
    have : (x < c * y) = (x < y) := by
      simp_all
      constructor
      · intro hcxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          exact lt_trans hx0 hy0
        next hy =>
          have : 0 < x := (pos_iff_neg_of_mul_neg hxy).mpr hy
          have : c * y < 0 := mul_neg_of_pos_of_neg hc hy
          linarith
      · intro hxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          have : 0 < c * y := Left.mul_pos hc hy0
          linarith
        next hy0 => nlinarith
    rw[this]
  grind

theorem variation_mult_pos (c d x y : ℝ) (hc : c > 0) (hd: d > 0): variation (c * x) (d*y) = variation x y := by
  simp_all [variation_mult_pos1, variation_mult_pos2]

lemma variation_cases (x y: ℝ):
      (x > 0 ∧ y > 0 -> variation x y = 0) ∧
      (x > 0 ∧ y < 0 -> variation x y = -1) ∧
      (x < 0 ∧ y > 0 -> variation x y = 1) ∧
      (x < 0 ∧ y < 0 -> variation x y = 0) := by
  unfold variation
  repeat' constructor
  · rintro ⟨hx, hy⟩;
    have  hxy : x * y ≥ 0 := by nlinarith
    simp [hxy]
  · rintro ⟨hx, hy⟩;
    have hxy: ¬ (x * y >= 0) := by nlinarith
    have hyltx: y <= x := by linarith
    simp [hxy, hyltx]
  · rintro ⟨hx, hy⟩ 
    have hxy: ¬ (x * y >= 0) := by nlinarith
    have hygtx: x < y := by linarith
    simp [hxy, hygtx]
  · rintro ⟨hx, hy⟩
    have hxy: x * y ≥ 0 := by nlinarith
    simp [hxy]

lemma variation_mult_neg_1 (c x y: ℝ) (hc: c < 0): variation (c*x) y = variation x y + if y = 0 then 0 else sgn x := by
  rcases lt_trichotomy x 0 with hxz | hxz | hxz <;> rcases lt_trichotomy y 0 with hyz | hyz | hyz
  · have : c * x > 0 := by nlinarith
    have hyy: y ≠ 0 := by linarith;
    have hxx: ¬ 0 < x := by linarith
    have hxnez: x ≠ 0 := by linarith
    simp [variation_cases, sgn, *]
  · simp_all [variation]
  · have : c * x > 0 := by nlinarith
    have hyy: y ≠ 0 := by linarith
    have hxx: ¬ 0 < x := by linarith
    have hxnez: x ≠ 0 := by linarith
    simp [variation_cases, sgn, *]
  · simp_all [variation, sgn]
  · simp_all [variation]
  · simp_all [variation, sgn]
  · have : c * x < 0 := by nlinarith
    have hyy: y ≠ 0 := by linarith
    simp [variation_cases, sgn, *]
  ·  simp_all [variation]
  · have : c * x < 0 := by nlinarith
    have hyy: y ≠ 0 := by linarith
    simp [variation_cases, sgn, *]

@[simp]
theorem cindex_poly_z_1 (p q: Polynomial ℝ) (a b: ℝ) (hp: p = 0) : cauchyIndex p q a b  = 0 := by 
  simp [cauchyIndex, jump_val, hp]

@[simp]
theorem cindex_poly_z_2 (p q: Polynomial ℝ) (a b: ℝ) (hq: q = 0) : cauchyIndex p q a b  = 0 := by
  simp [cauchyIndex, jump_val, hq]

theorem cindex_poly_const (p q: Polynomial ℝ) (a b x: ℝ) (hp_const: C x = p): cauchyIndex p q a b = 0 := by
  have hp_nroots : p.roots = 0 := by rw [<-hp_const]; exact roots_C x
  simp_all only [cauchyIndex, rootsInInterval, Set.mem_Ioo, Multiset.toFinset_zero, Finset.filter_empty, Finset.sum_empty]

theorem cindex_poly_mult {p q p': Polynomial ℝ} {a b: ℝ} (hp' : p' ≠ 0) :
    (cauchyIndex (p' * p) (p' * q) a b) = cauchyIndex p q a b := by
  if hp: p = 0 then
    simp [hp]
  else
    unfold cauchyIndex
    simp only [ne_eq, not_false_eq_true, jump_poly_mult, hp']
    have : ∑ x ∈ rootsInInterval p' a b \ rootsInInterval p a b, jump_val p q x = 0 := by
      apply Finset.sum_eq_zero
      intros x hx
      simp only [Finset.mem_sdiff] at hx
      unfold rootsInInterval at hx
      have : eval x p ≠ 0 := by
        have ⟨hx_1, hx_2⟩ := hx
        simp_all
      exact jump_poly_not_root this
    have h_interval : rootsInInterval (p' * p) a b = rootsInInterval p a b ∪ (rootsInInterval p' a b \ rootsInInterval p a b) := by
      unfold rootsInInterval
      simp_all only [ne_eq, Set.mem_Ioo, Finset.union_sdiff_self_eq_union]
      ext a_1 : 1
      simp_all only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, mul_eq_zero, or_self,
        not_false_eq_true, IsRoot.def, eval_mul, true_and, Finset.mem_union]
      apply Iff.intro
      · intro a_2
        simp_all only [and_self, and_true]
        obtain ⟨left, right⟩ := a_2
        obtain ⟨left_1, right⟩ := right
        cases left with
        | inl h => simp_all only [or_true]
        | inr h_1 => simp_all only [true_or]
      · intro a_2
        cases a_2 with
        | inl h => simp_all only [or_true, and_self]
        | inr h_1 => simp_all only [true_or, and_self]
    simp only [h_interval]
    have hdsj : Disjoint (rootsInInterval p a b) (rootsInInterval p' a b \ rootsInInterval p a b) := by
      exact Finset.disjoint_sdiff
    rw [Finset.sum_union hdsj]
    simp [this]

theorem cindex_poly_cross {p : Polynomial ℝ} {a b: ℝ} (hab: a < b) (hpa_nroot: eval a p ≠ 0) (hpb_nroot: eval b p ≠ 0) :
    cauchyIndex p 1 a b = cross p a b := by
  have hpz : p ≠ 0 := by
    simp_all only [ne_eq]
    intro a_1
    subst a_1
    simp_all only [eval_zero, not_true_eq_false]
  induction hp: p.natDegree using Nat.strong_induction_on generalizing p with
  | _ k ih  =>
    cases k with
    | zero =>
      have hp_const : ∃ x: ℝ, C x = p := natDegree_eq_zero.mp hp 
      have ⟨x, hx⟩ := hp_const
      have hlz: cauchyIndex p 1 a b = 0 := cindex_poly_const p 1 a b x hx
      have hrz: cross p a b = 0 := by
        unfold cross variation
        have h_eq : eval a p = eval b p := by
          subst hx
          simp_all only [not_lt_zero', ne_eq, cindex_poly_z_1, not_isEmpty_of_nonempty, IsEmpty.forall_iff,
            implies_true, eval_C, not_false_eq_true, map_eq_zero, natDegree_C, C_inj, exists_eq, cindex_poly_const]
        simp [h_eq]
        exact mul_self_nonneg (eval b p)
      rw [hlz, hrz]
      | succ k =>
        if H: (rootsInInterval p a b).Nonempty then
          let maxr : ℝ := Finset.max' (rootsInInterval p a b) H
          have hmaxr_root : eval maxr p = 0 ∧ maxr > a ∧  maxr < b := by
            have : maxr ∈ rootsInInterval p a b := Finset.max'_mem (rootsInInterval p a b) H
            unfold rootsInInterval at this; aesop
          let maxrp := (X - C maxr)^ (rootMultiplicity maxr p)
          have ⟨p', hp'⟩ : ∃p': Polynomial ℝ, p = p' * maxrp := by
            have : maxrp ∣ p := by
              unfold maxrp
              exact pow_rootMultiplicity_dvd p maxr
            exact exists_eq_mul_left_of_dvd this
          have hmonon_nvdv : ¬ (X - C maxr ∣ p') := by
            by_contra!
            have : (X - C maxr)^(rootMultiplicity maxr p + 1) ∣ p := by
              unfold maxrp at hp';
              have ⟨p'', hp''⟩ : ∃ p'' : Polynomial ℝ, p' = p'' * (X - C maxr) := exists_eq_mul_left_of_dvd this
              rw [hp'', mul_right_comm, mul_assoc, <-pow_succ] at hp';
              exact Dvd.intro_left p'' (id (Eq.symm hp'))
            have h_contra := (le_rootMultiplicity_iff hpz).mpr this
            linarith
          have ⟨hp'z, maxrpz, hap', hbp', hamaxrp, hbmaxrp⟩ :
             p' ≠ 0 ∧ maxrp ≠ 0 ∧ eval a p' ≠ 0 ∧ eval b p' ≠ 0 ∧ eval a maxrp ≠ 0 ∧ eval b maxrp ≠ 0 := by
            repeat' constructor
            · rw [hp'] at hpz; exact left_ne_zero_of_mul hpz
            · rw [hp'] at hpz; exact right_ne_zero_of_mul hpz
            · rw [hp', eval_mul] at hpa_nroot; simp_all
            · rw [hp', eval_mul] at hpb_nroot; simp_all
            · rw [hp', eval_mul] at hpa_nroot; simp_all
            · rw [hp', eval_mul] at hpb_nroot; simp_all
          have hmaxrp' : eval maxr p' ≠ 0 := (not_imp_not.mpr (dvd_iff_isRoot.mpr)) hmonon_nvdv
          have hmulrz: rootMultiplicity maxr p > 0 := ((rootMultiplicity_pos hpz).mpr (IsRoot.def.mpr hmaxr_root.1))
          have hmulr : rootMultiplicity maxr p ≠ 0 := (zero_lt_iff.mp hmulrz)
          let maxr_sign := if Odd (rootMultiplicity maxr p) then -1 else 1
          have hc_sum: cauchyIndex p 1 a b = (∑x∈ (rootsInInterval p' a b), jump_val p 1 x) + jump_val p 1 maxr := by
            unfold cauchyIndex
            have hrinterval : rootsInInterval p a b = rootsInInterval p' a b ∪ rootsInInterval maxrp a b := by
              unfold rootsInInterval
              rw [hp'] at hpz ⊢; exact rootsInInterval_mul a b hpz; 
            have hmaxrp_singleton : rootsInInterval maxrp a b = {maxr} := by
              unfold maxrp rootsInInterval
              simp_all
            have hdisjoint : rootsInInterval p' a b ∩ rootsInInterval maxrp a b = ∅ := by
              have : maxr ∉ rootsInInterval  p' a b := by
                by_contra!
                unfold rootsInInterval at this;
                have : maxr ∈ p'.roots := by simp_all
                have : X - C maxr ∣ p' := dvd_iff_isRoot.mpr (isRoot_of_mem_roots this)
                exact hmonon_nvdv this
              rw [hmaxrp_singleton]
              simp [this]
            rw [hrinterval, Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr hdisjoint), hmaxrp_singleton]
            simp
          have hcross : ∑(x ∈ rootsInInterval p' a b), jump_val p 1 x = maxr_sign * cross p' a b := by
            have hcr_sign : ∑ (x ∈ rootsInInterval p' a b), jump_val p 1 x = ∑ (x∈ rootsInInterval p' a b), maxr_sign * jump_val p' 1 x := by
              refine Finset.sum_congr rfl ?_
              intros x hx
              have hx_root: x ∈ rootsInInterval p a b := by
                rw [hp'] at hpz ⊢
                rw [rootsInInterval_mul a b hpz]
                simp [hx]
              have hx_maxr : x ≠ maxr := by
                by_contra!
                rw [this] at hx
                have hx : maxr ∈ roots p' := by
                  unfold rootsInInterval at hx
                  simp_all
                exact hmonon_nvdv (dvd_iff_isRoot.mpr (isRoot_of_mem_roots hx))
              have hx_nroot: eval x maxrp ≠ 0 := by
               unfold maxrp
               rw [eval_pow]
               have : eval x (X - C maxr) ≠ 0 := by
                 have : ¬ (IsRoot (X - C maxr) x) := by
                   exact (not_imp_not.mpr (root_X_sub_C (a := maxr) (b := x).mp)) (id (Ne.symm hx_maxr))
                 rw [IsRoot.def] at this
                 exact this
               exact pow_ne_zero (rootMultiplicity maxr p) this
              have hxlmaxr: x < maxr := by
                have : x <= maxr := Finset.le_max' (rootsInInterval p a b) x hx_root 
                exact lt_of_le_of_ne this hx_maxr
              have hmaxr_sign : sgn (eval x maxrp) = maxr_sign := by
                unfold sgn maxr_sign 
                simp [hx_nroot]
                unfold maxrp
                have hevallt: (x - maxr) < 0 := by
                  simp [hxlmaxr]
                split_ifs with h₁ h₂ h₃
                · have hcontra: ¬ 0 < eval x ((X - C maxr) ^ rootMultiplicity maxr p) := by
                    simp
                    exact (Odd.pow_nonpos_iff h₂).mpr (le_of_lt hevallt)
                  exact hcontra h₁
                · rfl
                · rfl
                · have h_contra : 0 < eval x ((X - C maxr) ^ rootMultiplicity maxr p) := by
                    simp at h₃ ⊢
                    exact (Even.pow_pos_iff h₃ hmulr).mpr (sub_ne_zero_of_ne hx_maxr)
                  exact h₁ h_contra
              rw [hp', jump_poly_1_mult (Or.inr hx_nroot), hmaxr_sign]
              simp [jump_poly_not_root hx_nroot]
            have hsec: ∑ (x∈ rootsInInterval p' a b), maxr_sign * jump_val p' 1 x = maxr_sign * (∑ x∈ rootsInInterval p' a b, jump_val p' 1 x) :=
              Eq.symm (Finset.mul_sum (rootsInInterval p' a b) (jump_val p' 1) maxr_sign)
            have hthird: maxr_sign * (∑ x∈ rootsInInterval p' a b, jump_val p' 1 x) = maxr_sign * cross p' a b:= by
              if H': rootsInInterval p' a b = ∅ then
                simp [H']
                exact Or.inr (cross_no_root hab H')
              else
                have hpp'_deg: p'.natDegree < p.natDegree := by
                  rw [hp', natDegree_mul hp'z maxrpz];
                  unfold maxrp
                  simp [hmulrz]
                have hcindex: cauchyIndex p' 1 a b = cross p' a b := by
                  rw [<-hp] at ih
                  exact ih p'.natDegree hpp'_deg hap' hbp' hp'z rfl 
                have hf: cauchyIndex p' 1 a b = ∑ (x ∈ rootsInInterval p' a b), jump_val p' 1 x := by
                  unfold cauchyIndex
                  rfl
                rw [<-hf, hcindex]
            rw [hcr_sign, hsec, hthird]
          have hcross_jp: maxr_sign * cross p' a b + jump_val p 1 maxr = cross p a b := by
            if H': Odd (rootMultiplicity maxr p) then
              have hamaxrpltz: eval a maxrp < 0 := by
                unfold maxrp
                simp
                have : a - maxr < 0 := by linarith
                exact Odd.pow_neg H' this
              have hbmaxrpgtz: eval b maxrp > 0 := by
                unfold maxrp
                simp
                have : b - maxr > 0 := by linarith
                exact pow_pos this (rootMultiplicity maxr p)
              have hr: cross p a b = cross p' a b + sgn (eval a p') := by
                rw [hp', cross, eval_mul, eval_mul, cross, mul_comm]
                rw [variation_mult_neg_1 (eval a maxrp) (eval a p') ((eval b p') * (eval b maxrp)) hamaxrpltz]
                rw [mul_comm, variation_mult_pos2 (eval b maxrp) (eval a p') (eval b p') hbmaxrpgtz]
                have : eval b maxrp * eval b p' ≠ 0 := by
                  exact mul_ne_zero hbmaxrp hbp'
                simp [this]
              have hl: maxr_sign * cross p' a b + jump_val p 1 maxr = - cross p' a b + sgn (eval b p') := by
                have hsrpos: (sign_r_pos maxr p') = (eval maxr p' > 0) := by
                  rw [sign_r_pos_rec p' maxr hp'z]
                  simp [hmaxrp'] 
                have hn: (eval maxr p' > 0) = (eval b p' > 0) := by
                  by_contra!
                  have hprodz: (eval maxr p') * (eval b p') < 0 := by
                      clear *- hmaxrp' this hbp'
                      if H'': eval maxr p' > 0 then
                        simp [H''] at this
                        have haux: eval b p' < 0 := lt_of_le_of_ne this hbp'
                        nlinarith
                      else
                        simp [H''] at this
                        have haux: eval maxr p' < 0 := by simp at H''; exact lt_of_le_of_ne H'' hmaxrp'
                        nlinarith
                  have ⟨r, hr, ⟨hrmaxr, hrp'⟩⟩ : ∃r:ℝ, (r > maxr) ∧ ( r < b) ∧ (eval r p' = 0):= by
                    clear *- hprodz hmaxr_root
                    have ⟨_, ⟨_, hmaxrb⟩⟩ := hmaxr_root
                    have hmaxrb: maxr ≤ b := le_of_lt hmaxrb
                    exact exists_root_ioo_mul hmaxrb hprodz
                  have hrint: r ∈ rootsInInterval p a b := by
                    clear *- hp' hr hrmaxr hrp' hp'z hmaxr_root hpz
                    have haux: r ∈ rootsInInterval p' a b := by
                      have ⟨_, ⟨hamaxrb, hmaxrb⟩⟩ := hmaxr_root
                      unfold rootsInInterval
                      have ha: a < r := by linarith
                      simp_all
                    rw [hp'] at hpz ⊢
                    rw [rootsInInterval_mul a b hpz]
                    simp_all
                  clear *- hr hrmaxr hrp' hmaxr_root hrint
                  have : ¬ r > maxr := by
                    simp
                    unfold maxr
                    exact Finset.le_max' (rootsInInterval p a b) r hrint
                  exact this hr
                have hsrposmaxr: sign_r_pos maxr maxrp := by
                  unfold maxrp
                  exact sign_r_pos_power maxr (rootMultiplicity maxr p)
                unfold maxr_sign jump_val sgn
                have haux: rootMultiplicity maxr 1 = 0 := by simp
                simp [H', haux, hpz]
                rw [mul_one, hp', sign_r_pos_mult p' maxrp maxr hp'z maxrpz, hsrpos, hn]
                simp [hbp', hsrposmaxr]
              have hvar: variation (eval a p') (eval b p') + sgn (eval a p') = (-variation (eval a p') (eval b p')) + (sgn (eval b p')) := by
                clear *- hap' hbp'
                unfold sgn
                rcases lt_trichotomy (eval b p') 0 with hxz | hxz | hxz <;> rcases lt_trichotomy (eval a p') 0 with hyz | hyz | hyz
                · have ⟨hasgn, hbsgn⟩ :  (¬ 0 < eval a p') ∧ (¬ 0 < eval b p'):= by constructor <;> linarith
                  simp [variation_cases, *]; 
                · exfalso; exact hap' hyz 
                · have hbsgn :(¬ 0 < eval b p') := by linarith
                  simp [variation_cases, *]
                · exfalso; exact hbp' hxz
                · exfalso; exact hbp' hxz
                · exfalso; exact hbp' hxz
                · have : ¬ 0 < eval a p' := by linarith
                  simp [variation_cases, *]
                · exfalso; exact hap' hyz
                . simp [variation_cases, *]
              rw [hr, hl]
              unfold cross
              exact (Eq.symm hvar)
            else
              simp at H'
              have ⟨hapos, hbpos⟩ : eval a maxrp > 0 ∧ eval b maxrp > 0 := by
                unfold maxrp
                rw [eval_pow, eval_pow] 
                constructor
                · simp
                  have : a - maxr ≠ 0 := by clear *-hmaxr_root; linarith
                  exact Even.pow_pos H' this
                · simp
                  have :  b - maxr ≠ 0 := by clear *-hmaxr_root; linarith
                  exact Even.pow_pos H' this
              have hr: cross p a b = cross p' a b := by
                unfold cross
                rw [hp', eval_mul, eval_mul]
                rw [mul_comm, variation_mult_pos1 (eval a maxrp) (eval a p') (eval b p' * eval b maxrp) hapos,  mul_comm, variation_mult_pos2 (eval b maxrp) (eval a p') (eval b p') (hbpos)]
              unfold maxr_sign jump_val
              have h_aux: rootMultiplicity maxr 1 = 0 := by simp
              have h_aux2: ¬ Odd (rootMultiplicity maxr p) := by simp [H']
              simp [h_aux2, h_aux, hpz]
              exact (Eq.symm hr)
          rw [hc_sum, hcross, hcross_jp]
        else  
          have hlz : cauchyIndex p 1 a b = 0 := by
            unfold cauchyIndex; aesop
          simp at H
          rw [hlz, cross_no_root hab H]

theorem cindex_poly_inverse_add {p q: Polynomial ℝ} (a b: ℝ) (hpq_coprime: IsCoprime p q) : cauchyIndex p q a b + cauchyIndex q p a b = cauchyIndex (q * p) 1 a b := by
  if hpqz: p = 0 ∨ q = 0 then
   rcases hpqz with hp | hq <;> simp_all
  else
    push_neg at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    let A := rootsInInterval p a b
    let B := rootsInInterval q a b
    have hl: cauchyIndex p q a b + cauchyIndex q p a b = ∑ x ∈ A, jump_val (q * p) 1 x + ∑ x ∈ B, jump_val (q*p) 1 x := by
      have hf: cauchyIndex p q a b = ∑ x ∈ A, jump_val (q * p) 1 x := by
        unfold A cauchyIndex 
        refine Finset.sum_congr rfl ?_
        intros x hx
        unfold rootsInInterval at hx
        have : eval x p = 0 := by aesop
        exact jump_poly_coprime this hpq_coprime
      have hs: cauchyIndex q p a b = ∑ x ∈ B, jump_val (q * p) 1 x := by
       unfold B cauchyIndex
       refine Finset.sum_congr rfl ?_
       intros x hx
       unfold rootsInInterval at hx
       have : eval x q = 0 := by aesop
       have hqp_coprime: IsCoprime q p := id (IsCoprime.symm hpq_coprime)
       rw [mul_comm]
       exact jump_poly_coprime this hqp_coprime
      linarith
    have hab_union : A ∪ B = rootsInInterval (q * p) a b := by
      unfold A B rootsInInterval
      aesop
    have hab_disjoint' : A ∩ B = ∅ := by
      if H: A = ∅ ∨ B = ∅ then aesop
      else
        by_contra!
        have hy: ∃ y: ℝ, y ∈ A ∧ y ∈ B := by
         simp only [not_or, <-Finset.nonempty_iff_ne_empty] at H this
         exact Finset.filter_nonempty_iff.mp this
        have ⟨y, hy⟩ := hy
        have h_eval : eval y p = 0 ∧ eval y q = 0 := by
          unfold A B rootsInInterval at hy
          simp_all
        have h_monom: (X - C y) ∣ p ∧ (X - C y) ∣ q := by
            simp [dvd_iff_isRoot, h_eval]
        have h_monon_dvd : (X - C y) ∣ gcd p q := (dvd_gcd_iff (X - C y) p q).mpr h_monom
        have hf : ¬IsUnit (gcd p q)  := by
          by_contra!
          rw [isUnit_iff] at this; have ⟨r, hr⟩ := this
          have h_contra :¬ X - C y ∣ (gcd p q) := by
            rw [<-hr.2]
            refine not_dvd_of_degree_lt ?_ ?_
            · aesop
            · have hrz : r ≠ 0 := isUnit_iff_ne_zero.mp hr.1
              rw [degree_C hrz];
              exact (Monic.degree_pos (monic_X_sub_C y)).mpr (X_sub_C_ne_one y)
          exact h_contra h_monon_dvd
        exact hf ((gcd_isUnit_iff p q).mpr hpq_coprime)
    have hab_disjoint : (Disjoint A B) := Finset.disjoint_iff_inter_eq_empty.mpr hab_disjoint'
    rw [hl]
    unfold cauchyIndex
    unfold A B at hab_disjoint hab_union
    rw [<-Finset.sum_union hab_disjoint, hab_union]

theorem cindex_poly_inverse_add_cross (p q : Polynomial ℝ) (a b : ℝ)
    (hab : a < b) (hapq : eval a (p*q) ≠ 0) (hbpq : eval b (p*q) ≠ 0) :
    cauchyIndex p q a b + cauchyIndex q p a b = variation (eval a (p * q)) (eval b (p*q)) := by
  have pneq0 : p ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  have qneq0 : q ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  let g := gcd p q
  have ⟨q', hq'⟩ : ∃q', q = g * q' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_right p q
  have ⟨p', hp'⟩ : ∃p', p = g * p' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_left p q
  have h_gcd : g ≠ 0 := by
    intro hfalse
    have : q = 0 := by simp [hq', hfalse]
    exact qneq0 this
  have cauchyMuls : cauchyIndex p q a b + cauchyIndex q p a b
      = cauchyIndex p' q' a b + cauchyIndex q' p' a b:= by
    rw [hp',hq']
    if h1p0 : p = 0 then exact False.elim (pneq0 h1p0)
    else
      rw [cindex_poly_mult h_gcd, cindex_poly_mult h_gcd]
  have cauchy1 : cauchyIndex p' q' a b + cauchyIndex q' p' a b
      = cauchyIndex (q' * p') 1 a b := by
        have : IsCoprime p' q' := (gcd_isUnit_iff p' q').mp (isUnit_gcd_of_eq_mul_gcd hp' hq' h_gcd)
        exact cindex_poly_inverse_add a b this
  have cauchyVar : cauchyIndex (p' * q') 1 a b
      = variation (eval a (p' * q'))  (eval b (p'*q')) := by
    have : cauchyIndex (p' * q') 1 a b = cross (p' * q') a b := by
      have ha : eval a (p' * q') ≠ 0 := by simp_all
      have hb : eval b (p' * q') ≠ 0 := by simp_all
      exact cindex_poly_cross hab ha hb
    exact this
  have : variation (eval a (p' * q'))  (eval b (p'*q')) =
         variation (eval a (p * q)) (eval b (p*q)) := by
    have t1 : eval a (p * q) = eval a (g*g) * eval a (p' * q') := by
      rw [hp', hq']
      simp only [eval_mul]
      linarith
    rw[t1]
    have t2 : eval b (p * q) = eval b (g*g) * eval b (p' * q') := by
      rw[hp', hq']
      simp only [eval_mul]
      linarith
    rw[t2]
    simp at hapq
    obtain ⟨hap, haq⟩ := hapq
    have hag : eval a g ≠ 0 := by
      intro abs
      rw [hp'] at hap
      simp at hap
      obtain ⟨hag, hap'⟩ := hap
      exact hag abs
    simp at hbpq
    obtain ⟨hbp, hbq⟩ := hbpq
    have hbg : eval b g ≠ 0 := by
      intro abs
      rw [hp'] at hbp
      simp at hbp
      obtain ⟨hbg, hbp'⟩ := hbp
      exact hbg abs
    have t3 : eval a (g*g) > 0 := by simp [hag]
    have t4 : eval b (g*g) > 0 := by simp [hbg]
    rw [variation_mult_pos (eval a (g * g)) (eval b (g * g)) (eval a (p' * q')) (eval b (p' * q')) t3 t4]
  rw [cauchyMuls, cauchy1, mul_comm, cauchyVar, <-this]

lemma cindex_poly_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (haa' : a < a') (hb'b : b' < b) (ha'b' : a' < b')
    (hpx : ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p ≠ 0) :
    cauchyIndex p q a b = cauchyIndex p q a' b' := by
  unfold cauchyIndex
  have : rootsInInterval p a b = rootsInInterval p a' b' := by
    rw [rootsInSet_interval]
    rw [rootsInSet_interval]
    have : Set.Ioo a b = Set.Ioc a a' ∪ Set.Ioo a' b' ∪ Set.Ico b' b := by
      rw [Set.Ioc_union_Ioo_eq_Ioo (le_of_lt haa') ha'b']
      rw [Set.Ioo_union_Ico_eq_Ioo (gt_trans ha'b' haa') (le_of_lt hb'b)]
    rw [this, <- rootsInSet_cup, <- rootsInSet_cup]
    have : rootsInSet p (Set.Ioc a a') = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | a < x ∧ x ≤ a'} := Finset.nonempty_def.mp this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inl (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    have : rootsInSet p (Set.Ico b' b) = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | b' ≤ x ∧ x < b} := Finset.nonempty_def.mp this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inr (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    simp
  rw [this]
