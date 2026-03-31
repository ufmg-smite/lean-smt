import Smt.Reconstruct.Real.CAD.Sturm.Utils

open Polynomial Set Filter Classical

noncomputable section

def rightNear (x : ℝ) : Filter ℝ := nhdsWithin x (Set.Ioi x)

def eventually_at_right (x : ℝ) (P : Real → Prop) : Prop :=
  Filter.Eventually P (rightNear x)

theorem eventually_at_right_equiv {x : Real} {P : Real -> Prop} : eventually_at_right x P ↔ (∃ b : Real, (b > x) ∧ (∀ y : Real, x < y ∧ y < b → P y)) := by
  constructor
  · intro hev
    simp [eventually_at_right] at hev
    exact mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  · intro h
    simp [eventually_at_right]
    exact mem_nhdsGT_iff_exists_Ioo_subset.mpr h

theorem eventually_at_right_def (x: ℝ) (P: ℝ -> Prop) : eventually_at_right x P = Filter.Eventually P (rightNear x) := by rfl

def sign_r_pos (x : ℝ) (p : Polynomial ℝ) : Prop := eventually_at_right x (fun x => eval x p > 0)

-- We should define sign_r_pos in terms of eventually_at_right
theorem eventually_at_right_equiv' {x : Real} {p : Polynomial Real} : sign_r_pos x p ↔ (∃ b : Real, (b > x) ∧ (∀ y : Real, x < y ∧ y < b → 0 < eval y p)) := by
  constructor
  · intro hev
    exact mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  · intro h
    simp [sign_r_pos]
    exact mem_nhdsGT_iff_exists_Ioo_subset.mpr h

theorem eventually_subst (P Q: ℝ → Prop) (F: Filter ℝ) (h: Filter.Eventually (fun a => P a  = Q a) F) :
    (Filter.Eventually P F = Filter.Eventually Q F) := by
  simp only [eq_iff_iff] at h ⊢
  constructor
  · intro hev
    exact (eventually_congr h).mp hev
  · intro hev'
    exact (eventually_congr h).mpr hev'

lemma sign_r_pos_rec (p : Polynomial Real) (x : Real) (hp : p ≠ 0) :
    sign_r_pos x p = if eval x p = 0 then sign_r_pos x (derivative p) else eval x p > 0 := by
  if hev : eval x p = 0 then
    have H1 : sign_r_pos x (derivative p) → sign_r_pos x p := by
      by_contra!
      obtain ⟨H1, H2⟩ := this
      obtain ⟨b, hb1, hb2⟩  := eventually_at_right_equiv'.mp H1
      have HF := (iff_false_right H2).mp (Iff.symm eventually_at_right_equiv')
      push_neg at HF
      obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := HF b hb1
      obtain ⟨z', hz1', hz2', hz3'⟩ := exists_deriv_eq_slope_poly x z hz1 p
      have abs1 : eval z' (derivative p) ≤ 0 := by
        rw [hev] at hz3'
        simp at hz3'
        have : 0 < z - x := by linarith
        clear * - hz3' this hz3
        simp_all only [ge_iff_le]
        exact nonpos_of_mul_nonpos_right hz3 this
      have abs2 := hb2 z' ⟨hz1', lt_trans hz2' hz2⟩
      linarith
    have H2 : sign_r_pos x p → sign_r_pos x (derivative p) := by
      intro H
      have : derivative p ≠ 0 := derivative_ne_0 p x hev hp
      obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval (derivative p) x this
      have H1 := (not_eq_pos_or_neg_iff_1 (derivative p) x ub).mp hub2
      simp at H1
      have : ¬ (∀ z : Real, x < z → z ≤ ub → eval z (derivative p) < 0) := by
        intro abs
        rw [eventually_at_right_equiv'] at H
        obtain ⟨ub', hub1', hub2'⟩ := H
        let T := (x + (min ub ub')) / 2
        have hx1 : 2 * x < (x + ub) := by linarith
        have hx2 : 2 * x < (x + ub') := by linarith
        have hx3 : 2 * x < min (x + ub) (x + ub') := lt_min hx1 hx2
        have hx4 : min (x + ub) (x + ub') = x + min ub ub' := min_add_add_left x ub ub'
        have : x < T := by
          simp only [T]
          rw [<- hx4]
          linarith
        obtain ⟨z', hz1', hz2', hz3'⟩ := exists_deriv_eq_slope_poly x T this p
        clear hx1 hx2 hx3 hx4
        have hT : 0 < eval T p := by
          refine hub2' T ⟨this, ?_⟩
          simp [T]
          if Hub : ub < ub' then
            rw [min_eq_left_of_lt Hub]
            linarith
          else
            push_neg at Hub
            rw [min_eq_right Hub]
            linarith
        have : 0 < T - x := by linarith
        rw [hev] at hz3'
        simp at hz3'
        have : 0 < eval z' (derivative p) := by
          clear * -  this hz3' hT
          have foo : 0 < (T - x) * eval z' (derivative p) := lt_of_lt_of_eq hT hz3'
          exact (pos_iff_pos_of_mul_pos foo).mp this
        have foo : z' ≤ ub := by
          simp [T] at hz2'
          if Hub : ub < ub' then
            rw [min_eq_left_of_lt Hub] at hz2'
            linarith
          else
            push_neg at Hub
            rw [min_eq_right Hub] at hz2'
            linarith
        have := abs z' hz1' foo
        linarith
      have : ∀ z : Real, x < z → z ≤ ub → 0 < eval z (derivative p) := by
        cases H1
        next H1 => exact False.elim (this H1)
        next H1 => exact H1
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      exact this y hy1 (le_of_lt hy2)
    simp [hev]
    exact ⟨H2, H1⟩
  else
    simp [hev]
    have : sign_r_pos x p → 0 < eval x p := by
      by_contra!
      obtain ⟨h1, h2⟩ := this
      obtain ⟨ub, hub1, hub2⟩  : ∃ ub : Real, x < ub ∧ (∀ z : Real, z > x ∧ z < ub → 0 < eval z p) := by
        obtain ⟨ub, hub1, hub2⟩  := eventually_at_right_equiv'.mp h1
        use ub
      have H : 0 < eval ((ub + x) / 2) p := by
        have h1 : ((ub + x) / 2) > x := by linarith
        have h2 : ((ub + x) / 2) < ub := by linarith
        exact hub2 ((ub + x) / 2) ⟨h1, h2⟩
      have H2 : eval x p < 0 := lt_of_le_of_ne h2 hev
      obtain ⟨r, hr1, hr2, hr3⟩ := exists_root_interval p x ((ub + x) / 2) (by linarith) (le_of_lt H2) (le_of_lt H)
      have : r ≠ x := by
        intro abs
        rw [<- abs] at hev
        exact hev hr3
      have : x < r := lt_of_le_of_ne hr1 (Ne.symm this)
      have := hub2 r ⟨this, by linarith⟩
      linarith
    have : 0 < eval x p → sign_r_pos x p := by
      intro H
      rw [eventually_at_right_equiv']
      obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
      have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
      cases this
      next H1 =>
        clear hub2
        apply False.elim
        have : eval ub p < 0 := H1 ub (by simp; exact hub1)
        obtain ⟨r, hr1, hr2, hr3⟩ :=
          exists_root_interval (-p) x ub (le_of_lt hub1) (by simp; exact le_of_lt H) (by simp; exact le_of_lt this)
        simp at hr3
        by_cases x = r
        next heq =>
          rw [<- heq] at hr3
          rw [hr3] at H
          simp at H
        next hneq =>
          have : x < r := lt_of_le_of_ne hr1 hneq
          have : r ∈ Ioc x ub := by simp; aesop
          have := H1 r this
          rw [hr3] at this
          simp at this
      next H1 =>
        use ub
        refine ⟨hub1, ?_⟩
        rintro y ⟨hy1, hy2⟩
        simp at H1
        exact H1 y hy1 (le_of_lt hy2)
    simp_all only [ne_eq]
    apply Iff.intro <;> intro a <;> simp_all only [imp_self, forall_const]

lemma sign_r_pos_minus (x : ℝ) (p : Polynomial ℝ) : p ≠ 0 → (sign_r_pos x p ↔ (¬ sign_r_pos x (-p))) := by
  intro hp
  have : sign_r_pos x p ∨ sign_r_pos x (-p) := by
    obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
    have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
    cases this
    next H =>
      right
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      simp at H ⊢
      exact H y hy1 (le_of_lt hy2)
    next H =>
      left
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      simp at H
      exact H y hy1 (le_of_lt hy2)
  have : sign_r_pos x p → ¬ (sign_r_pos x (-p)) := by
    intros H abs
    rw [eventually_at_right_equiv'] at H abs
    obtain ⟨b, hb1, hb2⟩ := H
    obtain ⟨c, hc1, hc2⟩ := abs
    let s := min b c
    have xs : x < s := lt_min hb1 hc1
    let y := (x + s) / 2
    have xy : x < y := left_lt_add_div_two.mpr xs
    have ys : y < s := add_div_two_lt_right.mpr xs
    have sb : s ≤ b := min_le_left b c
    have yb : y < b := Std.lt_of_lt_of_le ys sb
    have sc : s ≤ c := min_le_right b c
    have yc : y < c := Std.lt_of_lt_of_le ys sc
    have h1 := hb2 y ⟨xy, yb⟩
    have h2 := hc2 y ⟨xy, yc⟩
    simp at h2
    linarith
  aesop

lemma sign_r_pos_mult (p q : Polynomial Real) (x : Real) (hp : p ≠ 0) (hq : q ≠ 0) :
    sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
  obtain ⟨ub, hub1, hub2⟩ : ∃ ub : ℝ , x < ub ∧ ((∀ z ∈ Ioo x ub, 0 < eval z p) ∨ (∀ z ∈ Ioo x ub, eval z p < 0)) := by
    obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
    have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
    replace this : (∀ z ∈ Set.Ioo x ub, eval z p < 0) ∨ (∀ z ∈ Set.Ioo x ub, 0 < eval z p) := by
      cases this
      next H =>
        left
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
      next H =>
        right
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
    use ub
    exact ⟨hub1, (Or.symm this)⟩
  obtain ⟨ub', hub1', hub2'⟩ : ∃ ub' : ℝ , x < ub' ∧ ((∀ z ∈ Ioo x ub', 0 < eval z q) ∨ (∀ z ∈ Ioo x ub', eval z q < 0)) := by
    obtain ⟨ub', hub1', hub2'⟩ := next_non_root_interval q x hq
    have := (not_eq_pos_or_neg_iff_1 q x ub').mp hub2'
    replace this : (∀ z ∈ Set.Ioo x ub', eval z q < 0) ∨ (∀ z ∈ Set.Ioo x ub', 0 < eval z q) := by
      cases this
      next H =>
        left
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
      next H =>
        right
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
    use ub'
    exact ⟨hub1', (Or.symm this)⟩
  have H1 : (∀ z ∈ Ioo x ub, 0 < eval z p) → (∀ z ∈ Ioo x ub', 0 < eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x p := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      exact And.symm ⟨hzp, hub1⟩
    have sign_r_pos_q : sign_r_pos x q := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      exact And.symm ⟨hzq, hub1'⟩
    have : Filter.Eventually (fun z => 0 < eval z p ∧ 0 < eval z q) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z p ∧ 0 < eval z q) (q := fun z => 0 < eval z (p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      exact Left.mul_pos hx₁ hx₂
    simp_all only [ne_eq, mem_Ioo, and_self, implies_true, and_imp, true_or, eventually_and]
  have H2 : (∀ z ∈ Ioo x ub, 0 < eval z p) → (∀ z ∈ Ioo x ub', 0 > eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x p := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      exact And.symm ⟨hzp, hub1⟩
    have sign_r_pos_q : sign_r_pos x (-q) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      simp_all only [ne_eq, mem_Ioo, and_self, implies_true, and_imp, true_or, or_true, true_iff, eq_iff_iff,
        forall_const, gt_iff_lt, eval_neg, Left.neg_pos_iff]
    have : Filter.Eventually (fun z => 0 < eval z p ∧ 0 < eval z (-q)) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (- p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z p ∧ 0 < eval z (-q)) (q := fun z => 0 < eval z (-p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      have hp : eval x (-p) < 0 := by simp; exact hx₁
      have hq : eval x q < 0 := by simp at hx₂; exact hx₂
      exact mul_pos_of_neg_of_neg hp hq
    have : ¬ sign_r_pos x (p * q) := by
      have eq : p * q = - (-p * q) := by
        clear * -
        simp_all only [neg_mul, neg_neg]
      rw [eq]
      have neq0 : p * q ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp
      have neq0' : -p * q ≠ 0 := by
        clear * - neq0
        simp_all only [ne_eq, mul_eq_zero, not_or, neg_mul, neg_eq_zero, or_self, not_false_eq_true]
      exact (sign_r_pos_minus x (-p * q) neq0').mp this
    have sign_r_pos_q' : ¬ sign_r_pos x q := by
      clear * -  sign_r_pos_q hq
      have := sign_r_pos_minus x q hq
      exact (not_congr (id (Iff.symm this))).mp fun a => a sign_r_pos_q
    clear * - this sign_r_pos_p sign_r_pos_q'
    simp_all only [iff_false, not_true_eq_false]
  have H3 : (∀ z ∈ Ioo x ub, 0 > eval z p) → (∀ z ∈ Ioo x ub', 0 < eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x (-p) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      simp_all only [ne_eq, mem_Ioo, and_imp, and_self, implies_true, or_true, true_or, eq_iff_iff, forall_const,
        gt_iff_lt, eval_neg, Left.neg_pos_iff]
    have sign_r_pos_q : sign_r_pos x q := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      exact And.symm ⟨hzq, hub1'⟩
    have : Filter.Eventually (fun z => 0 < eval z (-p) ∧ 0 < eval z q) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (- p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z (-p) ∧ 0 < eval z q) (q := fun z => 0 < eval z (-p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      exact Left.mul_pos hx₁ hx₂
    have : ¬ sign_r_pos x (p * q) := by
      have eq : p * q = - (-p * q) := by
        clear * -
        simp_all only [neg_mul, neg_neg]
      rw [eq]
      have neq0 : p * q ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp
      have neq0' : -p * q ≠ 0 := by
        clear * - neq0
        simp_all only [ne_eq, mul_eq_zero, not_or, neg_mul, neg_eq_zero, or_self, not_false_eq_true]
      exact (sign_r_pos_minus x (-p * q) neq0').mp this
    have sign_r_pos_p' : ¬ sign_r_pos x p := by
      have := sign_r_pos_minus x p hp
      exact (not_congr (id (Iff.symm this))).mp fun a => a sign_r_pos_p
    clear * - this sign_r_pos_p' sign_r_pos_q
    simp_all only [iff_true]
  have H4 : (∀ z ∈ Ioo x ub, 0 > eval z p) → (∀ z ∈ Ioo x ub', 0 > eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x (-p) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      simp_all only [ne_eq, mem_Ioo, and_imp, and_self, implies_true, or_true, gt_iff_lt, eq_iff_iff, forall_const,
        eval_neg, Left.neg_pos_iff]
    have sign_r_pos_q : sign_r_pos x (-q) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      simp_all only [ne_eq, mem_Ioo, and_imp, and_self, implies_true, or_true, gt_iff_lt, eq_iff_iff, forall_const,
        eval_neg, Left.neg_pos_iff]
    have : Filter.Eventually (fun z => 0 < eval z (-p) ∧ 0 < eval z (-q)) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z (-p) ∧ 0 < eval z (-q)) (q := fun z => 0 < eval z (p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      simp at hx₁
      simp at hx₂
      exact mul_pos_of_neg_of_neg hx₁ hx₂
    clear * - this sign_r_pos_p sign_r_pos_q hp hq
    have : ¬ sign_r_pos x p := by
      have := sign_r_pos_minus x p hp
      exact (not_congr (Iff.symm this)).mp fun a => a sign_r_pos_p
    have : ¬ sign_r_pos x q := by
      have := sign_r_pos_minus x q hq
      exact (not_congr (Iff.symm this)).mp fun a => a sign_r_pos_q
    simp_all only [ne_eq]
  simp_all only [ne_eq, mem_Ioo, and_imp, implies_true, eq_iff_iff, gt_iff_lt]
  cases hub2 <;> cases hub2' <;> simp_all only [implies_true, forall_const]

lemma sign_r_pos_deriv (p : Polynomial Real) (x : Real) (hp : p ≠ 0) (hev : eval x p = 0) : sign_r_pos x (derivative p * p) := by
  have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
  suffices sign_r_pos x (derivative p) = sign_r_pos x p by
    rw [sign_r_pos_mult (derivative p) p x deriv_ne_0 hp]
    exact Eq.to_iff this
  rw [sign_r_pos_rec p]
  · simp [hev]
  · exact hp

lemma sign_r_pos_add {x : ℝ} (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
    (sign_r_pos x (p + q) = sign_r_pos x q) := by
  by_cases (eval x (p + q) = 0)
  next => aesop
  next hf =>
    have h_pq : p + q ≠ 0 := eval_non_zero (p + q) x hf
    have h: sign_r_pos x (p + q) = (eval x q > 0) := by
      have := sign_r_pos_rec (p + q) x h_pq
      simp [hp_eval, hq_eval] at this; simp [this]
    have : sign_r_pos x q = (eval x q > 0) := by
      have := sign_r_pos_rec q x (eval_non_zero q x hq_eval)
      simp [hq_eval] at this; simp [this]
    simp [this, h]

lemma sign_r_pos_mod {x : ℝ} (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
    sign_r_pos x (q % p) = sign_r_pos x q := by
  have h' : eval x (q % p) ≠ 0 := by rw [eval_mod q p x hp_eval]; exact hq_eval
  nth_rw 2 [<-EuclideanDomain.div_add_mod q p]
  rw [sign_r_pos_add]
  · simp only [eval_mul, mul_eq_zero]; exact Or.inl hp_eval
  · exact h'

lemma sign_r_pos_smult (p: Polynomial ℝ) (x c: ℝ) : (c ≠ 0) -> (p ≠ 0) ->
  sign_r_pos x (Polynomial.C c * p) = if c > 0 then sign_r_pos x p else ¬ sign_r_pos x p := by
  intros hc hp
  by_cases (c > 0)
  next ht => simp [sign_r_pos, ht]
  next hf =>
    simp [hf]
    simp at hf hc
    have hcltz : c < 0 := lt_of_le_of_ne hf hc
    have hy : ∀y: ℝ, ((0 < eval y (C c * p)) = (0 < eval y (-p) )) := by
      simp_all
      intro y
      constructor
      · exact fun a => neg_of_mul_pos_right a hf
      · exact fun a => mul_pos_of_neg_of_neg hcltz a
    have heq : sign_r_pos x (C c * p) = sign_r_pos x (-p) := by
      simp [sign_r_pos]
      aesop
    have : sign_r_pos x p = (¬ sign_r_pos x (-p)) := by simp only [sign_r_pos_minus x p hp]
    aesop

lemma sign_r_pos_power (a: ℝ) (n: ℕ): sign_r_pos a ((X - C a)^n) := by
  induction n with
  | zero => rw [eventually_at_right_equiv']; simp; exact exists_gt a
  | succ n ih =>
    have hd: (derivative ((X - C a)^(n + 1)) = (C (n + 1: ℝ)) *  (X - C a)^n)  := by 
      rw [derivative_X_sub_C_pow]
      simp
    have hnz: ((X - C a)^ (n + 1)) ≠ 0 := by
       have : X - C a ≠ 0 := X_sub_C_ne_zero a
       exact pow_ne_zero (n + 1) this
    have hnz': ((X - C a)^ (n)) ≠ 0 := by
       have : X - C a ≠ 0 := X_sub_C_ne_zero a
       exact pow_ne_zero (n) this
    have heval: eval a ((X - C a)^ (n + 1)) = 0 := by simp
    have hsrpos1: sign_r_pos  a ((X - C a)^ (n + 1)) = (sign_r_pos a ((C (n + 1: ℝ)) *  ((X - C a)^n))) := by
      rw [sign_r_pos_rec ((X - C a)^ (n + 1)) a hnz, hd]
      simp [heval]
    have hsrpos2: sign_r_pos  a ((X - C a)^ (n + 1)) = sign_r_pos  a ((X - C a)^ n) := by
      have haux : (n + 1: ℝ) ≠ 0 := by linarith
      have haux': (n + 1: ℝ) > 0 := by linarith
      rw [ne_eq] at hnz
      rw [hsrpos1, sign_r_pos_smult ((X - C a) ^ n) a (n + 1: ℝ) haux hnz']
      simp [haux']
    rw [<- hsrpos2] at ih
    exact ih

