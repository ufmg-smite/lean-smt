import Smt.Reconstruct.Real.CAD.Sturm.SignRPos

open Polynomial Set Filter Classical

noncomputable section

-- 1 if p / q goes from -inf to +inf at x, -1 if goes from +inf to -inf
-- 0 otherwise
def jump_val (p q : Polynomial ℝ) (x : ℝ) : ℤ :=
  let orderP : Nat := rootMultiplicity x p
  let orderQ : Nat := rootMultiplicity x q
  let oddOrder := Odd (orderP - orderQ)
  if p ≠ 0 ∧ q ≠ 0 ∧ oddOrder then
    -- note that p * q > 0 is the same as p / q > 0
    if sign_r_pos x (p * q) then 1 else -1
  else 0

lemma jump_poly_mult {p q p': Polynomial ℝ} {x: ℝ} (hp': p' ≠ 0) :
                    jump_val (p' * p) (p'* q) x = jump_val p q x := by
  by_cases (q = 0 ∨ p = 0)
  next H =>
    unfold jump_val; simp only;
    cases H <;> simp_all
  next H =>
  rw [not_or] at H; obtain ⟨hp, hq⟩ := H
  have h_sign : sign_r_pos x (p' * q * (p' * p)) = sign_r_pos x (q * p) := by
    have ⟨b, h_b⟩ : ∃b, b > x ∧ (∀z, x < z ∧ z < b -> eval z (p' * p') > 0)  := by
      rcases Classical.em (∃z, eval z p' = 0 ∧ z > x) with ⟨z, hz⟩ | hf
      · have roots_fin : {r: ℝ | eval r p' = 0 ∧ r > x}.Finite := by
          have := finite_setOf_isRoot hp'
          unfold IsRoot at this; exact Finite.sep this fun a => a > x
        let roots_x : Finset ℝ := Finite.toFinset roots_fin
        have : roots_x.Nonempty := by
          unfold roots_x; simp; exact Set.nonempty_of_mem hz
        let lr := Finset.min' (roots_x) this
        have h_eval_nz: (∀z: ℝ, x < z ∧ z < lr -> eval z p' ≠ 0) ∧ lr > x := by
          have : lr > x := by
            unfold lr; unfold roots_x;
            simp
          simp only [this, and_true]
          intros z hz; unfold lr roots_x at hz
          have hz_n : z ∉ roots_x := by
            by_contra!
            simp [roots_x] at this hz
            simp [this] at hz; have h_contra := hz z this.1 this.2
            exact (lt_self_iff_false z).mp h_contra
          simp [roots_x, hz] at hz_n; exact hz_n
        have h_eval_gz : ∀z: ℝ, x < z ∧ z < lr ->  eval z (p' * p') > 0 := by
          intros z hz; simp; exact h_eval_nz.1 z hz
        use lr; exact ⟨h_eval_nz.2, h_eval_gz⟩
      · have h_eval_nz: ∀z:ℝ, x < z ∧ z < x + 1 -> eval z p' ≠ 0 := by
          intros z hz; simp at hf
          have := (hf z)
          contrapose this; simp at this ⊢
          exact ⟨this, hz.1⟩
        have h_eval_gz: ∀z:ℝ, x < z ∧ z < x + 1 -> eval z (p' * p') > 0 := by
          intros z hz; simp; exact h_eval_nz z hz
        have h_trivial : x + 1 > x := lt_add_one x
        use x+1
    have h_bb : ∃b, b > x ∧ ∀z: ℝ, x < z ∧ z < b -> ((0 < eval z (p' * q * (p' * p))) = (0 < eval z (q * p))) := by
        use b; simp only [h_b, true_and];
        intros z hz; simp; have := h_b.2 z hz
        simp only [eval_mul] at this; ring_nf at this ⊢
        simp [gt_iff_lt] at this
        have ans := mul_pos_iff_of_pos_left (b := eval z q * eval z p) this
        ring_nf at ans; exact ans
    simp only [eventually_at_right_equiv']
    have := eventually_subst (fun a => eval a (p' * q * (p' * p)) > 0)  (fun a => eval a (q * p) > 0) (rightNear x)
    simp only [<-eventually_at_right_def, eventually_at_right_equiv] at this
    exact this h_bb
  have h_odd : Odd (rootMultiplicity x (p' * p) - rootMultiplicity x (p' * q)) =
               Odd (rootMultiplicity x p - rootMultiplicity x q) := by
    have hp'p : p' * p ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp'
    have hp'q : p' * q ≠ 0 := (mul_ne_zero_iff_right hp).mpr hp'
    simp [rootMultiplicity_mul hp'q, rootMultiplicity_mul hp'p]
    rw [Nat.add_sub_add_left]
  simp_all only [jump_val, ne_eq, eq_iff_iff, mul_eq_zero, or_self, not_false_eq_true, true_and,
    Int.reduceNeg, mul_comm]

lemma jump_poly_mod (p q: Polynomial ℝ) (x: ℝ) : jump_val p q x = jump_val p (q % p) x := by
  by_cases (p = 0 ∨ q = 0)
  next => aesop
  next hf =>
    simp [<- ne_eq] at hf
    let n := min (rootMultiplicity x q) (rootMultiplicity x p)
    have ⟨q', hq'⟩ : ∃q', q = (X - C x)^n * q' := by
      have  : (X - C x)^n ∣ q := by
        rw [<- le_rootMultiplicity_iff hf.2]
        exact Nat.min_le_left (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have ⟨p', hp'⟩ : ∃p', p = (X - C x)^n * p' := by
      have : (X - C x)^n ∣ p := by
        rw [<- (le_rootMultiplicity_iff hf.1)]
        exact Nat.min_le_right (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have hz' : q' ≠ 0 ∧ p' ≠ 0:= by
      rw [hq', hp'] at hf
      exact ⟨right_ne_zero_of_mul hf.2, right_ne_zero_of_mul hf.1⟩
    have hrm: rootMultiplicity x q' = 0 ∨ rootMultiplicity x p' = 0 := by
      if H: n = rootMultiplicity x q then
        have : ¬(X - C x)^1 ∣ q' := by
         simp
         have hbound := rootMultiplicity_le_iff hf.2 x n
         simp [H] at hbound
         by_contra!
         have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
         rw [hf, mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hq'
         have hcontra : (X - C x)^(n + 1) ∣ q := by
           simp [hq']
         rw [H] at hcontra
         exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.1 x 0] at this
        omega
      else
        have H : n = rootMultiplicity x p := by omega
        have : ¬(X - C x)^1 ∣ p' := by
          simp
          have hbound := rootMultiplicity_le_iff hf.1 x n
          simp [H] at hbound
          by_contra!
          have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
          rw [hf, mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hp'
          have hcontra : (X - C x)^(n + 1) ∣ p := by
            simp [hp']
          rw [H] at hcontra
          exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.2 x 0] at this
        omega
    have hcond: q' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x q') =
               ((q' % p' ≠ 0) ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p'))) := by
        by_cases (rootMultiplicity x p' = 0)
        next htt => simp [htt, hz']
        next hff =>
          rw [<-ne_eq] at hff
          rcases hrm with hok | hcontra
          · have hq_ndvd: ¬ ((X - C x)^1 ∣ q') := by
              apply (rootMultiplicity_le_iff hz'.1 x 0).mp
              linarith
            have hp_dvd : (X - C x) ∣ p' := by
              have : rootMultiplicity x p' >= 1:= by omega
              apply (le_rootMultiplicity_iff hz'.2).mp at this
              simp at this; exact this
            have hq_mod_ndvd : ¬ ((X - C x)^1 ∣ q' % p') := by
              simp at hq_ndvd ⊢
              simp [EuclideanDomain.dvd_mod_iff hp_dvd]; exact hq_ndvd
            have : rootMultiplicity x (q' % p') = 0 ∧ q' % p' ≠ 0 := by
              simp at hq_mod_ndvd hq_ndvd
              have : q' % p' ≠ 0 := by
                simp only [ne_eq, EuclideanDomain.mod_eq_zero]
                by_contra!
                exact hq_ndvd (dvd_trans hp_dvd this)
              constructor
              · apply Nat.le_zero.mp; apply (rootMultiplicity_le_iff this x 0).mpr
                simp
                exact hq_mod_ndvd
              · exact this
            simp [hz', this, hok]
          · exfalso; exact hff hcontra
    have h_imp : q' % p' ≠ 0 -> eval x p' = 0 -> sign_r_pos x (q' * p') = sign_r_pos x (q' % p' * p') := by
      intros h_mod_z h_eval_z
      have : eval x q' ≠ 0 := by
        simp_all [<- IsRoot.def, rootMultiplicity_eq_zero_iff]
      have : sign_r_pos x q' = sign_r_pos x (q' % p') := Eq.symm (sign_r_pos_mod p' q' h_eval_z this)
      rw [sign_r_pos_mult _ _ _ h_mod_z hz'.2, sign_r_pos_mult _ _ _ hz'.1 hz'.2];
      simp at this ⊢
      exact this
    have h: q' % p' = 0 ∨ eval x p' ≠ 0 -> jump_val p' q' x = jump_val p' (q' % p') x := by
      intros h_or
      if h_modz: (q' % p' = 0) then unfold jump_val; simp [*]
      else
        have : ¬ Odd (rootMultiplicity x p' - rootMultiplicity x q') ∧
               ¬ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p')) := by
          have h': eval x p' ≠ 0 := Or.resolve_left h_or h_modz
          simp [*] at hcond;
          have : rootMultiplicity x p' = 0 := rootMultiplicity_eq_zero h'
          have : ¬ Odd (rootMultiplicity x p' - rootMultiplicity x q') := by simp [this]
          simp [this] at hcond ⊢; exact hcond
        unfold jump_val; simp [*]
    have h_ult : jump_val p' q' x = jump_val p' (q' % p') x := by
      if h': (q' % p' ≠ 0 ∧ eval x p' = 0) then
      · have := (h_imp h'.1) h'.2
        unfold jump_val
        if hpz: (p' = 0) then simp [hpz] else
          simp only; split
          next H =>
            simp only [eq_iff_iff] at hcond; simp [(hcond.2.mp H.2.2), hpz]
            rw [mul_comm, this, mul_comm];
          next H =>
            simp only [Lean.Grind.not_and] at H;
            rcases H with ha | hb | hc <;> simp_all
       else
         simp only [Lean.Grind.not_and, not_not, <-ne_eq] at h'
         exact h h'
    clear *- h_ult hq' hp' hf hz'
    have h_mon_z :  (X - C x) ^ n ≠ 0:= by
      exact pow_ne_zero n (X_sub_C_ne_zero x)
    rw [hp', hq']
    have h_mod : ((X - C x)^n * q') % ((X - C x)^n * p') = (X - C x)^n * (q' % p') :=
      mod_mul q' p' ((X - C x) ^ n) h_mon_z
    simp [h_mod, jump_poly_mult h_mon_z]
    exact h_ult

lemma jump_poly_smult_1 (p q: Polynomial ℝ) (c x: ℝ) :
    jump_val p (Polynomial.C c * q) x = (sgn c) * jump_val p q x := by
  rcases Classical.em (c = 0 ∨ q = 0)  with ht|hf
  · simp [jump_val, ht]
    intros h1 h2 h3
    have hc: c = 0 := by aesop
    split
    · simp [sgn, hc]
    · simp [hc, sgn]
  · simp at hf
    unfold jump_val
    if hpz : p = 0 then simp [hpz]
    else
      have h := sign_r_pos_smult (p * q) x c hf.1
      simp [hf, hpz] at h
      simp [hpz, hf]
      unfold sgn
      have := mul_C_eq_root_multiplicity q c x hf.1
      rw [mul_left_comm, this]
      if hc : c > 0 then
        simp [hc] at h ⊢
        rw [h]
     else
       simp [hc, hf.1] at h ⊢
       simp only [h, ite_not]

@[simp]
lemma jump_poly_not_root {p q: Polynomial ℝ} {x: ℝ} (hp: eval x p ≠ 0) : jump_val p q x = 0 := by
  unfold jump_val
  have hpz: p ≠ 0 := eval_non_zero p x hp
  if hqz: q = 0 then
    simp [hqz, hpz]
  else
    have : rootMultiplicity x p = 0 := by simp [hp]
    simp [hpz, hqz, this]

@[simp]
lemma jump_poly_z1 (p: Polynomial ℝ) (x: ℝ) : jump_val p 0 x = 0 := by simp [jump_val]

@[simp]
lemma jump_poly_z2 (q: Polynomial ℝ) (x: ℝ) : jump_val 0 q x = 0 := by simp [jump_val]

lemma jump_poly_coprime {p q: Polynomial ℝ} {x: ℝ} (hp: eval x p = 0) (hpq_coprime : IsCoprime p q) : jump_val p q x = jump_val (q*p) 1 x := by
  if hpqz: (p = 0 ∨ q  = 0) then
    rcases hpqz with h | h <;> simp[h]
  else
    push_neg at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    have hroot : eval x p ≠ 0 ∨ eval x q ≠ 0 := aeval_ne_zero_of_isCoprime hpq_coprime x
    have hq_root : eval x q ≠ 0 := by aesop
    have hq_multiplicity : rootMultiplicity x q = 0 := by aesop
    have h: rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x (p * q) := by
      have : p * q ≠ 0 := mul_ne_zero_iff.mpr hpqz
      have := rootMultiplicity_mul (x := x) this
      rw [hq_multiplicity] at this ⊢
      simp [this]
    unfold jump_val
    have h_one: rootMultiplicity x 1 = 0 := rootMultiplicity_C 1 x
    simp [hqz, h_one, h]
    rw [mul_comm]

lemma jump_poly_1_mult {p q: Polynomial ℝ} {x: ℝ} (hnroot: eval x p ≠ 0 ∨ eval x q ≠ 0) :
      jump_val (p * q) 1 x  = sgn (eval x q) * jump_val p 1 x + sgn (eval x p) * jump_val q 1 x := by
  if H: p = 0 ∨ q = 0 then
    rcases H with h | h <;> simp [h, sgn]
  else
    have ⟨hpz, hqz, hpqz⟩ : p ≠ 0 ∧ q ≠ 0 ∧ p * q ≠ 0 := by simp_all
    rcases hnroot with h₁ | h₂
    · have hx_multiplicity : rootMultiplicity x p = 0 := by aesop
      let simpl := if q ≠ 0 ∧ Odd (rootMultiplicity x q) then if (eval x p > 0) ↔ sign_r_pos x q then 1 else -1 else 0
      have h_util: rootMultiplicity x 1 = 0 := by simp_all only [or_self, not_false_eq_true, ne_eq, mul_eq_zero,
        rootMultiplicity_eq_zero_iff, IsRoot.def, implies_true, eval_one, one_ne_zero]
      have hl_simpl : jump_val (p * q) 1 x = simpl := by
        unfold simpl jump_val
        simp [hpqz, rootMultiplicity_mul, h_util, sign_r_pos_mult, hpz, hqz, hx_multiplicity]
        rw [sign_r_pos_rec p x hpz]
        aesop
      have hpgtz: eval x p > 0 -> simpl = sgn (eval x q) * jump_val p 1 x + sgn (eval x p) * jump_val q 1 x := by
        intros hp
        unfold simpl
        simp only [ne_eq, gt_iff_lt, Int.reduceNeg, h₁, not_false_eq_true, jump_poly_not_root, mul_zero, zero_add]
        unfold jump_val sgn
        simp [hqz, hp, h_util]
      have hpltz: eval x p < 0 -> simpl = sgn (eval x q) * jump_val p 1 x + sgn (eval x p) * jump_val q 1 x := by
        intros hp
        unfold simpl
        have haux : ¬ eval x p > 0 := not_lt_of_gt hp
        simp only [ne_eq, gt_iff_lt, Int.reduceNeg, h₁, not_false_eq_true, jump_poly_not_root, mul_zero, zero_add]
        unfold jump_val sgn
        simp [hqz, haux, h_util, h₁]
      rw [hl_simpl]
      if H: eval x p > 0 then exact hpgtz H
      else
        have : eval x p < 0 := by
          push_neg at H
          exact lt_of_le_of_ne H h₁
        exact hpltz this
    · have hx_multiplicity : rootMultiplicity x q = 0 := by aesop
      let simpl := if p ≠ 0 ∧ Odd (rootMultiplicity x p) then if (eval x q > 0) ↔ sign_r_pos x p then 1 else -1 else 0
      have h_util: rootMultiplicity x 1 = 0 := by aesop
      have hl_simpl : jump_val (p * q) 1 x = simpl := by
        unfold simpl jump_val
        simp [hpqz, rootMultiplicity_mul, h_util, sign_r_pos_mult, hpz, hqz, hx_multiplicity]
        rw [sign_r_pos_rec q x hqz]
        simp_all only [or_self, not_false_eq_true, ne_eq, mul_eq_zero, rootMultiplicity_eq_zero_iff, IsRoot.def,
          implies_true, eval_one, one_ne_zero, ↓reduceIte, gt_iff_lt, Int.reduceNeg]
        split
        next h =>
          split
          next h_1 => simp_all only [↓reduceIte]
          next h_1 =>
            simp_all only [Int.reduceNeg, right_eq_ite_iff, reduceCtorEq, imp_false]
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [not_true_eq_false]
        next h => simp_all only [Nat.not_odd_iff_even]
      have hpgtz: eval x q > 0 -> simpl = sgn (eval x q) * jump_val p 1 x + sgn (eval x p) * jump_val q 1 x := by
        intros hq
        unfold simpl
        simp only [ne_eq, gt_iff_lt, Int.reduceNeg, h₂, not_false_eq_true, jump_poly_not_root, mul_zero]
        unfold jump_val sgn
        simp [hq, h_util]
      have hpltz: eval x q < 0 -> simpl = sgn (eval x q) * jump_val p 1 x + sgn (eval x p) * jump_val q 1 x := by
        intros hq
        unfold simpl
        have haux : ¬ eval x q > 0 := not_lt_of_gt hq
        simp only [ne_eq, gt_iff_lt, Int.reduceNeg, h₂, not_false_eq_true, jump_poly_not_root, mul_zero]
        unfold jump_val sgn
        simp [haux, h_util, h₂]
      rw [hl_simpl]
      if H: eval x q > 0 then
        exact hpgtz H
      else
      have : eval x q < 0 := by
        push_neg at H
        exact lt_of_le_of_ne H h₂
      exact hpltz this

lemma jump_poly_sign (p q : Polynomial ℝ) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jump_val p (derivative p * q) x = sgn (q.eval x) := by
  intros hp hev
  if hq : q = 0 then
    rw [hq]
    simp [sgn, jump_val]
  else
    have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
    have elim_p_order : rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
      rw [Polynomial.rootMultiplicity_mul]
      · rw [derivative_rootMultiplicity_of_root hev]
        have : 1 ≤ rootMultiplicity x p := by
          apply (Polynomial.le_rootMultiplicity_iff hp).mpr
          simp
          exact dvd_iff_isRoot.mpr hev
        omega
      · exact (mul_ne_zero_iff_right hq).mpr deriv_ne_0
    have elim_sgn_r_pos_p : sign_r_pos x (p * (derivative p * q)) = sign_r_pos x q := by
      have : sign_r_pos x (p * (derivative p * q)) = (sign_r_pos x (derivative p * p) ↔ sign_r_pos x q) := by
        have := sign_r_pos_mult (p * derivative p) q x ((mul_ne_zero_iff_right deriv_ne_0).mpr hp) hq
        nth_rw 2 [mul_comm p (derivative p)] at this
        rw [<- mul_assoc]
        exact this
      rw [this]
      have := sign_r_pos_deriv p x hp hev
      simp_all only [ne_eq, true_iff, eq_iff_iff]
    let simpleL : Int :=
      if derivative p * q ≠ 0 ∧ Odd (1 - rootMultiplicity x q) then
        (if sign_r_pos x q then 1 else -1)
      else 0
    have : jump_val p (derivative p * q) x = simpleL := by
      simp [jump_val, simpleL, hp, deriv_ne_0, hq, elim_p_order, elim_sgn_r_pos_p]
    rw [this]
    by_cases eval x q = 0
    next hevQ =>
      have : 0 < rootMultiplicity x q := (rootMultiplicity_pos hq).mpr hevQ
      have : 1 - rootMultiplicity x q = 0 := by omega
      have : ¬ Odd (1 - rootMultiplicity x q) := by rw [this]; exact Nat.not_odd_zero
      have lhs : simpleL = 0 := by
        simp [simpleL, this]
      have rhs : sgn (eval x q) = 0 := by rw [hevQ]; simp [sgn]
      rw [lhs, rhs]
    next hevQ =>
      have : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hevQ
      have h1 : Odd (1 - rootMultiplicity x q) := by
        rw [this]
        exact Nat.odd_iff.mpr rfl
      have h2 : derivative p * q ≠ 0 := by
        clear * - hq deriv_ne_0
        intro abs
        simp_all only [ne_eq, mul_eq_zero, or_self]
      have h3 : sign_r_pos x q ↔ 0 < eval x q := by
        rw [sign_r_pos_rec]
        simp [hevQ]
        exact hq
      have h4 : simpleL = if 0 < eval x q then 1 else -1 := by
        simp [simpleL, h1, h2, h3]
      rw [h4]
      simp [sgn, hevQ]
