import Smt.Reconstruct.Real.CAD.Sturm.SeqDefs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Set Filter Classical

noncomputable section

lemma or_neg_of_mul_neg (a b : ℝ) : a * b < 0 → a < 0 ∨ b < 0 := by
  intro h
  apply or_iff_not_imp_left.mpr
  intro ha
  nlinarith

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

lemma sgn_sgn_neg : ∀ x : ℝ, sgn x < 0 ↔ x < 0 := by
  intro x
  unfold sgn
  split_ifs
  next h =>
    simp only [Int.reduceLT, false_iff, not_lt]
    exact le_of_lt h
  next h1 h2 => simp [h2]
  next h1 h2 =>
    simp only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one, true_iff]
    push_neg at h1 h2
    exact lt_of_le_of_ne h1 h2

lemma sgn_sgn_zero : ∀ x : ℝ, sgn x = 0 ↔ x = 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp only [one_ne_zero, false_iff]; exact ne_of_gt h
  next h => simp [h]
  next h1 h2 => simp [h2]

lemma sgn_sgn_pos : ∀ x : ℝ, sgn x > 0 ↔ x > 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp [h]
  next h1 h2 => simp [h2]
  next h1 h2 => simp [h1]

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sgn (g.eval x)

lemma rootsInIntervalZero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by simp [rootsInInterval]

@[simp]
def rootsInSet (p : Polynomial ℝ) (S : Set ℝ) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ S)

lemma rootsInSet_interval (p : Polynomial ℝ) (a b : ℝ) :
    rootsInInterval p a b = rootsInSet p (Set.Ioo a b) := by simp [rootsInInterval]

lemma rootsInSet_cup (p : Polynomial ℝ) (S T : Set ℝ) :
    rootsInSet p S ∪ rootsInSet p T = rootsInSet p (S ∪ T) := by
  simp only [rootsInSet, mem_union]
  exact Finset.filter_union_right (fun x => x ∈ S) (fun x => x ∈ T) p.roots.toFinset

lemma sgn_inf_comp (p : Polynomial ℝ) :
    sgn_neg_inf p = sgn_pos_inf (p.comp (-Polynomial.X)) := by
  by_cases Even p.natDegree
  next H =>
    simp [sgn_neg_inf, sgn_pos_inf, H]
  next H =>
    simp [sgn_neg_inf, sgn_pos_inf, H, sgn]
    simp_all only [Nat.not_even_iff_odd, Odd.neg_one_pow, neg_mul, one_mul, Int.reduceNeg, Left.neg_pos_iff]
    split_ifs
    · linarith
    · simp_all only [natDegree_zero, Nat.not_odd_zero]
    · rfl
    · simp_all only [natDegree_zero, Nat.not_odd_zero]
    · rfl
    · rfl
    · simp_all only [not_lt, neg_neg]
      have : 0 = p.leadingCoeff := by linarith
      have : p = 0 := leadingCoeff_eq_zero.mp (Eq.symm this)
      contradiction

lemma next_non_root_interval (p : Polynomial Real) (lb : Real) (hp : p ≠ 0) :
    ∃ ub : Real, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  by_cases ∃ r : Real, eval r p = 0 ∧ r > lb
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w > lb)
    if hS: Finset.Nonempty S then
      obtain ⟨lr, hlr⟩ := Finset.min_of_nonempty hS
      have : lr ∈ S := Finset.mem_of_min hlr
      simp [S] at this
      have H2 : ∀ z ∈ Ioo lb lr, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.notMem_of_lt_min hz2 hlr
        simp [S] at this
        have := this hp abs
        linarith
      use (lb + lr) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo lb lr := by
          simp
          constructor
          · exact hz1
          · linarith
        have := H2 z this
        exact this abs
    else
      use lb + 1
      simp only [lt_add_iff_pos_right, zero_lt_one, mem_Ioc, ne_eq, and_imp, true_and]
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, hp, abs, hz1]
      have : Finset.Nonempty S := by simp_all only [ne_eq, gt_iff_lt,
        Finset.not_nonempty_iff_eq_empty, Finset.notMem_empty]
      exact hS this
  next hr =>
    push_neg at hr
    use lb + 1
    simp only [lt_add_iff_pos_right, zero_lt_one, mem_Ioc, ne_eq, and_imp, true_and]
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

lemma last_non_root_interval (p : Polynomial Real) (ub : Real) (hp : p ≠ 0) :
    ∃ lb : Real, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  by_cases ∃ r : Real, eval r p = 0 ∧ r < ub
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w < ub)
    if hS: Finset.Nonempty S then
      obtain ⟨mr, hmr⟩ := Finset.max_of_nonempty hS
      have : mr ∈ S := Finset.mem_of_max hmr
      simp [S] at this
      have H2 : ∀ z ∈ Ioo mr ub, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.notMem_of_max_lt hz1 hmr
        simp [S] at this
        have := this hp abs
        linarith
      use (mr + ub) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo mr ub := by
          simp
          constructor
          · linarith
          · exact hz2
        have := H2 z this
        exact this abs
    else
      use ub - 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, abs, hz2, hp]
      have : Finset.Nonempty S := by simp_all only [ne_eq, Finset.not_nonempty_iff_eq_empty,
        Finset.notMem_empty]
      exact hS this
  next hr =>
    push_neg at hr
    use ub - 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

theorem exists_root_interval : ∀ p: Polynomial Real, ∀ (a b : ℝ), a <= b → eval a p <= 0 → 0 <= eval b p -> ∃ r: ℝ, r >= a ∧ r <= b ∧ eval r p = 0 := by
  intros p a b hab ha hb
  have intermediate_value_app := intermediate_value_Icc hab p.continuousOn
  have zero_in_image : 0 ∈ p.eval '' Set.Icc a b := by aesop
  obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
  use x

theorem exists_root_ioo {p: Polynomial ℝ} {a b : ℝ} (hab: a <= b) (hap: eval a p < 0) (hbp: eval b p > 0): ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  have intermediate_value_app := intermediate_value_Ioo hab p.continuousOn
  have zero_in_image : 0 ∈ p.eval '' Set.Ioo a b := by aesop
  obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
  use x

theorem exists_root_ioo' {p: Polynomial ℝ} {a b : ℝ} (hab: a <= b) (hap: eval a p > 0) (hbp: eval b p < 0): ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  have intermediate_value_app := intermediate_value_Ioo' hab p.continuousOn
  have zero_in_image : 0 ∈ p.eval '' Set.Ioo a b := by aesop
  obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
  use x

theorem exists_root_ioo_mul {p: Polynomial ℝ} {a b: ℝ} (hab: a ≤ b) (hap: (eval a p) * (eval b p) < 0) : ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  if H: eval a p > 0 then
    have haux: eval b p < 0 := by nlinarith
    exact exists_root_ioo' hab H haux
  else
    have haux1: eval b p > 0 := by nlinarith
    have haux: eval a p < 0 := by nlinarith
    exact exists_root_ioo hab haux haux1

lemma not_eq_pos_or_neg_iff_1 (p : Polynomial Real) (lb ub : Real) :
    (∀ z ∈ Ioc lb ub, eval z p ≠ 0) ↔ ((∀ z ∈ Ioc lb ub, eval z p < 0) ∨ (∀ z ∈ Ioc lb ub, 0 < eval z p)) := by
  by_contra!
  cases this
  next H =>
    obtain ⟨H₁, ⟨z₁, hz₁, hz₁'⟩, ⟨z₂, hz₂, hz₂'⟩⟩ := H
    have z1Neq0 : eval z₁ p ≠ 0 := by aesop
    have z1Pos : 0 < eval z₁ p := lt_of_le_of_ne hz₁' (id (Ne.symm z1Neq0))
    have z2Neg : eval z₂ p < 0 := lt_of_le_of_ne hz₂' (H₁ z₂ hz₂)
    by_cases z₁ < z₂
    next hle =>
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval (-p) z₁ z₂ (le_of_lt hle) (by simp; exact hz₁') (by simp; exact hz₂')
      simp at hr₃
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor <;> linarith
      exact H₁ r this hr₃
    next hge =>
      push_neg at hge
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval p z₂ z₁ hge (le_of_lt z2Neg) (le_of_lt z1Pos)
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
  next H =>
    obtain ⟨⟨z, hz1, hz2⟩, H₂⟩ := H
    cases H₂
    next H₂ =>
      have := H₂ z hz1
      linarith
    next H₂ =>
      have := H₂ z hz1
      linarith

lemma derivative_ne_0 (p : Polynomial Real) (x : Real) (hev : eval x p = 0) (hp : p ≠ 0) : derivative p ≠ 0 := by
  intro abs
  have := natDegree_eq_zero_of_derivative_eq_zero abs
  obtain ⟨c, hc⟩  := (natDegree_eq_zero.mp this)
  have : c ≠ 0 := by
    intro abs2
    rw [abs2] at hc
    rw [<- hc] at hp
    simp at hp
  rw [<- hc] at hev
  simp at hev
  exact this hev

lemma exists_deriv_eq_slope_poly (a b : Real) (hab : a < b) (p : Polynomial Real) :
    ∃ c : Real, c > a ∧ c < b ∧ eval b p - eval a p = (b - a) * eval c (derivative p) := by
  obtain ⟨c, hc1, hc2⟩ :=
    exists_deriv_eq_slope (a := a) (b := b) (fun x => eval x p) hab
      (Polynomial.continuousOn_aeval p) (Polynomial.differentiableOn_aeval p)
  simp at hc1
  obtain ⟨hc_low, hc_high⟩ := hc1
  use c
  refine ⟨hc_low, hc_high, ?_⟩
  rw [Polynomial.deriv] at hc2
  rw [hc2]
  have : (b - a) ≠ 0 := by linarith
  field_simp

lemma eval_mod (p q: Polynomial ℝ) (x: ℝ) (h: eval x q = 0) : eval x (p % q) = eval x p := by
 have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
 rw [<- eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma eval_non_zero (p: Polynomial ℝ) (x: ℝ) (h: eval x p ≠ 0) : p ≠ 0 := by
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [eval_zero, not_true_eq_false]

lemma mul_C_eq_root_multiplicity (p: Polynomial ℝ) (c r: ℝ) (hc: ¬ c = 0):
    (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [<-count_roots]
  rw [roots_C_mul]
  exact hc

theorem div_rem_zero {b c r: Polynomial ℝ} (h_rem: r.degree < b.degree) : (c * b + r)/ b = c := by
  rw [mul_comm]
  have h_b : b ≠ 0 := ne_zero_of_degree_gt h_rem
  if H: r = 0 then
   simp [H, h_b]
  else
    have h_stronger : (b * c + r)/b = c ∧ (b * c + r) % b = r := by
      by_contra!
      have h_div_mod: ((b * c + r)/b - c) * b = r - ((b * c + r)% b) := by
       ring_nf
       rw [eq_sub_iff_add_eq, add_rotate, ← eq_sub_iff_add_eq, sub_neg_eq_add]
       simp [EuclideanDomain.div_add_mod]; ring
      have : (b * c + r) / b ≠ c ∧ (b * c + r) % b ≠ r := by
        rw [<- if_false_left]
        split_ifs with H'
        · simp [H', eq_sub_iff_add_eq'] at h_div_mod
          exact this H' h_div_mod
        · intro h_contra
          simp [h_contra, h_b, sub_eq_iff_eq_add] at h_div_mod
          exact H' h_div_mod
      have h_mod_deg : degree ((b * c  + r) % b) < degree b := by
        refine degree_lt_degree ?_
        refine natDegree_mod_lt (b * c + r) ?_
        exact Nat.ne_zero_of_lt ((natDegree_lt_natDegree_iff H).mpr h_rem)
      have h_r : degree (r - (b * c + r)% b) < degree b := by
        have h_max := degree_sub_le r ((b * c + r) % b)
        exact lt_of_le_of_lt h_max (max_lt h_rem h_mod_deg)
      have h_lt_deg : degree b ≤ degree ((b * c + r) / b - c) + degree b := by
        refine le_add_of_nonneg_of_le ?_ ?_
        · exact zero_le_degree_iff.mpr (sub_ne_zero_of_ne this.1)
        · rfl
      have h_div_deg : degree ((b * c + r)/b - c) + degree b = degree (((b * c + r) / b - c) * b) := by
        exact Eq.symm degree_mul
      have h_deg_plus: degree ((b * c + r)/b - c) + degree b = degree (r - (b * c + r)%b) := by
        simp_all
      have h_final : b.degree ≤ degree (r - (b * c + r) % b) := by
        exact le_of_le_of_eq h_lt_deg h_deg_plus
      have h_contra: degree (r - (b * c + r) % b) < degree (r - (b * c + r) % b) := by
        exact Std.lt_of_lt_of_le h_r h_final
      exact (lt_self_iff_false (r - (b * c + r) % b).degree).mp h_contra
    exact h_stronger.1

theorem mul_cancel' {p q r: Polynomial ℝ} (hr: r ≠ 0) : (r * p) / (r * q) = p / q := by
  simp [mul_comm]
  if H: q.natDegree = 0 then
    have ⟨x, h_x⟩ := natDegree_eq_zero.mp H
    rw [<-h_x]
    rw [div_C_mul, mul_div_cancel_right₀ (hb := hr)]
    have : p/ C x = p / (C x * 1) := by rw [mul_one]
    rw [this, div_C_mul]; norm_num
  else
    have hq : q ≠ 0 := Ne.symm (ne_of_apply_ne natDegree fun a => H (id (Eq.symm a)))
    have : p = (p/q) * q + p % q := Eq.symm (EuclideanDomain.div_add_mod' p q)
    rw[this]; ring_nf
    if H': p % q = 0 then
      have h_ne_z : q * r ≠ 0 := (mul_ne_zero_iff_right hr).mpr hq
      simp [H']
      rw [mul_assoc, mul_div_cancel_right₀ (hb := h_ne_z), mul_div_cancel_right₀ (hb := hq)]
    else
      have h_mod_deg : natDegree (p % q) < natDegree q := by
        exact natDegree_mod_lt p H
      have h_mod_r_deg : natDegree ((p % q) * r) < natDegree (q * r) := by
        simp [natDegree_mul, H', hr, hq]
        exact h_mod_deg
      rw [div_rem_zero (degree_lt_degree h_mod_deg), mul_assoc, div_rem_zero (degree_lt_degree h_mod_r_deg)]

lemma mod_eq_sub_div {a b: Polynomial ℝ} : a % b = a - (a/b) * b := by
  have := EuclideanDomain.div_add_mod' a b
  exact eq_sub_of_add_eq' this

theorem mod_mul (p q r: Polynomial ℝ) (hr: r ≠ 0) : (r * p) % (r * q) = r * (p % q) := by
  have : (r * p) % (r * q) = r * p - ((r * p)/(r * q)) * (r * q) := by
    exact mod_eq_sub_div
  ring_nf at this
  rw [mul_cancel' hr, mul_assoc, <-mul_sub, mul_comm q (p/q), <- mod_eq_sub_div (a := p) (b := q)] at this
  exact this

lemma X_sub_C_ne_one (r : ℝ) : X - C r ≠ 1 := by
  rw [sub_eq_neg_add, add_comm, <-C_neg]
  exact X_add_C_ne_one (-r)

lemma rootsInInterval_mul {p q: Polynomial ℝ} (a b: ℝ) (hpq: p * q ≠ 0): rootsInInterval (p * q) a b = rootsInInterval p a b ∪ rootsInInterval q a b := by
  unfold rootsInInterval
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.filter_union (fun x => x ∈ Ioo a b) p.roots.toFinset q.roots.toFinset

lemma neg_neg_div (p q: Polynomial ℝ) : - (-p/q) = p/q := by
  have: -1 = (-1:ℝ)⁻¹ := Eq.symm inv_neg_one
  calc
    -(-p/q) = -(-1 * p / q) := by simp
    _ = -1 * (-1 * p / q)  := by simp
    _ = -1 * (C (-1) * p / q) := by simp
    _ = (C (-1:ℝ)) * (C (-1) * p / q) := by simp
    _ = (C (-1:ℝ)⁻¹) * (C (-1) * p / q) := by rw [<-this]
    _ = p/q := by
      have hCz : C (-1:ℝ) ≠ 0 := by simp
      rw [<- div_C_mul, mul_cancel' hCz]

lemma mod_minus (p q: Polynomial ℝ) : -p%q = -(p%q) := by
  rw [mod_eq_sub_div, mod_eq_sub_div] 
  ring_nf
  calc
    -p - -p / q * q = -p + (- (-p/q * q)) := by ring
    _ = -p + q * (-(-p/q)) := by ring
    _ = -p + q * (p/q) := by rw[neg_neg_div p q]

lemma bound_sgn_pos_inf (p : Polynomial ℝ) (hp : p ≠ 0) : ∃ ub : ℝ, ∀ x, x ≥ ub → sgn (eval x p) = sgn_pos_inf p := by
  have : p.degree = ((Polynomial.X : Polynomial ℝ) ^ p.natDegree).degree := by
    simp_all only [ne_eq, degree_pow, degree_X, nsmul_eq_mul, mul_one]
    exact degree_eq_natDegree hp
  have := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq p (Polynomial.X ^ p.natDegree) this
  simp only [eval_pow, eval_X, monic_X_pow, Monic.leadingCoeff, div_one] at this
  have h_sign :
      Filter.Tendsto (fun x => p.eval x / x ^ p.natDegree * p.leadingCoeff) Filter.atTop (nhds (p.leadingCoeff ^ 2)) := by
    simpa only [sq] using this.mul tendsto_const_nhds
  have lcoef_pos : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have : 0 < p.leadingCoeff ^ 2 := pow_two_pos_of_ne_zero lcoef_pos
  have ev_pos : Filter.Eventually (fun x => p.eval x / x ^ p.natDegree * p.leadingCoeff > 0) Filter.atTop := by
    apply h_sign.eventually
    apply lt_mem_nhds
    assumption
  obtain ⟨ub, hub⟩ := Filter.eventually_atTop.mp ev_pos
  simp [sgn_pos_inf]
  have h_sign_eq : ∀ x, 0 < x → p.eval x * p.leadingCoeff > 0 → sgn (p.eval x) = sgn (p.leadingCoeff) := by
    intros x hx h; unfold sgn; split_ifs <;> nlinarith;
  have mul_pos : ∀ x, 0 < x → ub ≤ x → eval x p * p.leadingCoeff > 0 := by
    intros x x_pos hx
    have x_pow_pos : x ^ p.natDegree > 0 := pow_pos x_pos p.natDegree
    have : eval x p / x ^ p.natDegree * p.leadingCoeff * x ^ p.natDegree > 0 := Left.mul_pos (hub x hx) x_pow_pos
    have eq : (eval x p / x ^ p.natDegree * x ^ p.natDegree) * p.leadingCoeff > 0 := by linarith
    have : (eval x p / x ^ p.natDegree) * x ^ p.natDegree = eval x p := div_mul_cancel₀ (eval x p) (Ne.symm (ne_of_lt x_pow_pos))
    rw [this] at eq
    exact eq
  if ub_pos: 0 < ub then
    use ub
    intros x hx
    exact h_sign_eq x (Std.lt_of_lt_of_le ub_pos hx) (mul_pos x (Std.lt_of_lt_of_le ub_pos hx) hx)
  else
    use 1
    intros x hx
    exact h_sign_eq x (by linarith) (mul_pos x (by linarith) (by linarith))

lemma bound_sgn_neg_inf (p : Polynomial ℝ) (hp : p ≠ 0) : ∃ lb : ℝ, ∀ x, x ≤ lb → sgn (eval x p) = sgn_neg_inf p := by
  obtain ⟨s, hs⟩ : ∃ s, p.eval s ≠ 0 := by
    contrapose! hp
    exact zero_of_eval_zero p hp
  let p' := Polynomial.comp p (-Polynomial.X)
  obtain ⟨s, hs⟩ : ∃ s, p'.eval s ≠ 0 := by
    use -s
    unfold p'
    simp
    assumption
  have : p' ≠ 0 := by
    intro abs
    have ev_0 : eval s p' = 0 := by
      rw [abs]
      simp
    exact hs ev_0
  obtain ⟨ub, hub⟩  := bound_sgn_pos_inf (Polynomial.comp p (-Polynomial.X)) this
  rw [sgn_inf_comp]
  use -ub
  intros x hx
  have := hub (-x) (by linarith)
  simp at this
  exact this

lemma root_ub (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ ub, (∀ x, eval x p = 0 → x < ub) ∧ (∀ x, x ≥ ub → sgn (eval x p) = sgn_pos_inf p) := by
  obtain ⟨ub1, hub1⟩ : ∃ ub1, ∀ x, eval x p = 0 → x < ub1 := by
    by_cases ∃ r, eval r p = 0
    next H =>
      let roots := p.roots.toFinset
      obtain ⟨r, hr⟩ := H
      have : r ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hr)
      have : roots.Nonempty := by tauto
      obtain ⟨max_r, hm⟩ := Finset.max_of_nonempty this
      have : ∀ x, eval x p = 0 → x ≤ max_r := by
        intros x hx
        have := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hx)
        exact Finset.le_max_of_eq this hm
      use max_r + 1
      intros x hx
      have := this x hx
      linarith
    next H =>
      use 0
      intros x hx
      aesop
  obtain ⟨ub2, hub2⟩ : ∃ ub2, ∀ x, x ≥ ub2 → sgn (eval x p) = sgn_pos_inf p := bound_sgn_pos_inf p hp
  let ub := Max.max ub1 ub2
  have : ub1 ≤ ub := le_max_left ub1 ub2
  have : ub2 ≤ ub := le_max_right ub1 ub2
  use ub
  constructor
  · intros x hx
    have := hub1 x hx
    linarith
  · intros x hx
    exact hub2 x (by linarith)

lemma root_lb (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ lb, (∀ x, eval x p = 0 → x > lb) ∧ (∀ x, x ≤ lb → sgn (eval x p) = sgn_neg_inf p) := by
  obtain ⟨lb1, hlb1⟩ : ∃ lb1, ∀ x, eval x p = 0 → x > lb1 := by
    by_cases ∃ r, eval r p = 0
    next H =>
      let roots := p.roots.toFinset
      obtain ⟨r, hr⟩ := H
      have : r ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hr)
      have : roots.Nonempty := by tauto
      obtain ⟨min_r, hm⟩ := Finset.min_of_nonempty this
      have : ∀ x, eval x p = 0 → x ≥ min_r := by
        intros x hx
        have := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hx)
        exact Finset.min_le_of_eq this hm
      use min_r - 1
      intros x hx
      have := this x hx
      linarith
    next H =>
      use 0
      intros x hx
      aesop
  obtain ⟨lb2, hlb2⟩ : ∃ lb2, ∀ x, x ≤ lb2 → sgn (eval x p) = sgn_neg_inf p := bound_sgn_neg_inf p hp
  let lb := Min.min lb1 lb2
  have : lb ≤ lb1 := min_le_left lb1 lb2
  have : lb ≤ lb2 := min_le_right lb1 lb2
  use lb
  constructor
  · intros x hx
    have := hlb1 x hx
    linarith
  · intros x hx
    exact hlb2 x (by linarith)

lemma root_list_ub (ps : List (Polynomial ℝ)) (a : ℝ) (h0 : 0 ∉ ps) :
    ∃ ub : ℝ,
      ((∀ p ∈ ps, ∀ x : ℝ, eval x p = 0 → x < ub) ∧
       (a < ub) ∧
       (∀ x : ℝ, x ≥ ub → ∀ p ∈ ps, sgn (eval x p) = sgn_pos_inf p)) := by
  cases ps
  next => simp; exact exists_gt a
  next p ps =>
    have p_not_zero : p ≠ 0 := Ne.symm (List.ne_of_not_mem_cons h0)
    have not_zero : 0 ∉ ps := List.not_mem_of_not_mem_cons h0
    obtain ⟨ub1, hub1, hub2, hub3⟩ := root_list_ub ps a not_zero
    obtain ⟨ub2, hub21, hub22⟩ := root_ub p p_not_zero
    let ub := Max.max ub1 ub2
    have : ub1 ≤ ub := le_max_left ub1 ub2
    have : ub2 ≤ ub := le_max_right ub1 ub2
    use ub
    constructor
    · intros pp hpp x hx
      have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
      cases this
      next hmem =>
        rw [hmem] at hx
        exact lt_sup_of_lt_right (hub21 x hx)
      next hmem => exact lt_sup_of_lt_left (hub1 pp hmem x hx)
    · constructor
      · linarith
      · intros x hx pp hpp
        have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
        cases this
        next hmem =>
          rw [hmem]
          exact hub22 x (by linarith)
        next hmem =>
          exact hub3 x (by linarith) pp hmem

lemma root_list_lb (ps : List (Polynomial ℝ)) (b : ℝ) (h0 : 0 ∉ ps) :
    ∃ lb : ℝ,
      ((∀ p ∈ ps, ∀ x : ℝ, eval x p = 0 → lb < x) ∧
       (lb < b) ∧
       (∀ x : ℝ, x ≤ lb → ∀ p ∈ ps, sgn (eval x p) = sgn_neg_inf p)) := by
  cases ps
  next => simp; exact exists_lt b
  next p ps =>
    have p_not_zero : p ≠ 0 := Ne.symm (List.ne_of_not_mem_cons h0)
    have not_zero : 0 ∉ ps := List.not_mem_of_not_mem_cons h0
    obtain ⟨lb1, hlb1, hlb2, hlb3⟩ := root_list_lb ps b not_zero
    obtain ⟨lb2, hlb21, hlb22⟩ := root_lb p p_not_zero
    let lb := Min.min lb1 lb2
    have : lb ≤ lb1 := min_le_left lb1 lb2
    have : lb ≤ lb2 := min_le_right lb1 lb2
    use lb
    constructor
    · intros pp hpp x hx
      have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
      cases this
      next hmem =>
        rw [hmem] at hx
        exact inf_lt_of_right_lt (hlb21 x hx)
      next hmem => exact inf_lt_of_left_lt (hlb1 pp hmem x hx)
    · constructor
      · exact inf_lt_of_left_lt hlb2
      · intros x hx pp hpp
        have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
        cases this
        next hmem =>
          rw [hmem]
          apply hlb22
          linarith
        next hmem =>
          apply hlb3
          · linarith
          · exact hmem

lemma seqVarI_seqVarR (is : List ℤ) : seqVarI is = seqVarR (is : List ℝ) := match is with
| [] => by simp [seqVarR, seqVarI]
| [i] => by simp [seqVarR, seqVarI]
| i1 :: i2 :: is => by
  simp [seqVarR, seqVarI]
  have IH1 := seqVarI_seqVarR (i1 :: is)
  have IH2 := seqVarI_seqVarR (i2 :: is)
  have IH3 := seqVarI_seqVarR is
  split_ifs
  next => finiteness
  next => simp_all only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, List.cons_append,
    List.nil_append]
  next H1 H2 => norm_cast at H2
  next H1 H2 => norm_cast at H2
  next => finiteness
