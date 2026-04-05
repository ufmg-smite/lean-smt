import CompPoly
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Raw
import Smt.Reconstruct.Real.CAD.Sturm.Theorem

open CompPoly

namespace AlgebraicNumber

def AlgNum : Type :=
  { a : Raw | a.wellDefined ∧ a.sgnDiff }

def AlgNum.l (a : AlgNum) : Rat := a.val.l
def AlgNum.r (a : AlgNum) : Rat := a.val.r
def AlgNum.p (a : AlgNum) : CPolynomial Rat := a.val.p

def AlgNum.refine (a : AlgNum) : AlgNum :=
  have h1 : a.val.refine.wellDefined := Raw.refine_wellDefined a.val a.prop.1 a.prop.2
  have h2 : a.val.refine.sgnDiff := Raw.refine_sgnDiff a.val a.prop.1 a.prop.2
  ⟨a.val.refine, And.intro h1 h2⟩

lemma AlgNum.lr (a : AlgNum) : a.l ≤ a.r := Raw.lr_wellDefined a.val a.prop.1

@[grind =]
lemma refine_val (a : AlgNum) : a.refine.val = a.val.refine := by trivial

lemma AlgNum.refine_bounds_l (a : AlgNum) : a.l ≤ a.refine.l := Raw.refine_bounds_l a.val a.prop.1
lemma AlgNum.refine_bounds_r (a : AlgNum) : a.refine.r ≤ a.r := Raw.refine_bounds_r a.val a.prop.1

@[simp]
def toSeq (a: AlgNum) : ℕ → ℚ := fun n =>
  match n with
  | 0 => (a.l + a.r) / 2
  | n + 1 =>
    let a' := a.refine
    toSeq a' n

lemma toSeq_bound : ∀ a : AlgNum, ∀ i : Nat, a.l ≤ toSeq a i ∧ toSeq a i ≤ a.r := by
  intros a i
  have := a.lr
  cases i
  next =>
    simp only [toSeq]
    constructor <;> linarith
  next i =>
    simp only [toSeq]
    have := toSeq_bound a.refine i
    have := a.refine_bounds_l
    have := a.refine_bounds_r
    grind

lemma toSeq_iterate (a : AlgNum) : ∀ n k : ℕ, toSeq a (n + k) = toSeq (AlgNum.refine^[n] a) k := by
  intro n
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    intro k
    rw [Nat.succ_add]
    simp only [toSeq]
    rw [ih a.refine k, Function.iterate_succ, Function.comp]

lemma refine_width (a : AlgNum) : a.refine.val.r - a.refine.l = (a.val.r - a.l) / 2 := by
  simp [AlgNum.refine]
  exact Raw.refine_width a.val

lemma refineN_width (a : AlgNum) : ∀ n : ℕ,
    (AlgNum.refine^[n] a).val.r - (AlgNum.refine^[n] a).l = (a.val.r - a.l) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp, refine_width, ih]
    rw [pow_succ]
    field_simp

lemma toSeq_in_refineN (a : AlgNum) (n i : ℕ) (hni : n ≤ i) :
    (AlgNum.refine^[n] a).l ≤ toSeq a i ∧ toSeq a i ≤ (AlgNum.refine^[n] a).r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hni
  rw [toSeq_iterate]
  exact toSeq_bound _ k

theorem toSeq_cauchy : ∀ a: AlgNum, IsCauSeq abs (toSeq a) := by
  intros a
  intro ε hε
  have hlr := a.lr
  have hwidth_nn : 0 ≤ a.r - a.l := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (a.r - a.l) / 2 ^ N < ε := by
    rcases eq_or_lt_of_le hwidth_nn with heq | hlt
    · exact ⟨0, by simp [← heq, hε]⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hlt) (show (1:ℚ)/2 < 1 by norm_num)
      refine ⟨N, ?_⟩
      have h2pos : (0 : ℚ) < 2 ^ N := pow_pos (by norm_num) N
      have := mul_lt_mul_of_pos_right hN hlt
      rwa [div_mul_cancel₀ _ (ne_of_gt hlt), one_div, inv_pow, mul_comm,
        ← div_eq_mul_inv] at this
  use N
  intro j hj
  have hbN := toSeq_in_refineN a N N le_rfl
  have hbj := toSeq_in_refineN a N j hj
  have hwidthN : (AlgNum.refine^[N] a).r - (AlgNum.refine^[N] a).l = (a.r - a.l) / 2 ^ N := refineN_width a N
  rw [abs_lt]
  constructor <;> nlinarith [hbN.1, hbN.2, hbj.1, hbj.2]

@[simp]
def AlgNum.toReal (a: AlgNum): ℝ :=
  Real.ofCauchy (CauSeq.Completion.mk ⟨toSeq a, toSeq_cauchy a⟩)

lemma toReal_bounds : ∀ a : AlgNum,  a.l ≤ a.toReal ∧ a.toReal ≤ a.r := by
  rintro a
  simp only [AlgNum.toReal]
  change (a.l : ℝ) ≤ Real.mk ⟨toSeq a, toSeq_cauchy a⟩ ∧
         Real.mk ⟨toSeq a, toSeq_cauchy a⟩ ≤ (a.r : ℝ)
  exact ⟨Real.le_mk_of_forall_le ⟨0, fun j _ => by exact_mod_cast (toSeq_bound a j).1⟩,
         Real.mk_le_of_forall_le ⟨0, fun j _ => by exact_mod_cast (toSeq_bound a j).2⟩⟩

theorem refine_toReal : ∀ a : AlgNum, a.toReal = a.refine.toReal := by
  intro a
  simp only [AlgNum.toReal]
  apply Real.ext_cauchy
  exact CauSeq.Completion.mk_eq.mpr (by
    show CauSeq.LimZero _
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (a.r - a.l) / 2 ^ N < ε := by
      have hlr := a.lr
      have hwidth_nn : 0 ≤ a.r - a.l := by linarith
      rcases eq_or_lt_of_le hwidth_nn with heq | hlt
      · exact ⟨0, by simp [← heq, hε]⟩
      · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hlt) (show (1:ℚ)/2 < 1 by norm_num)
        refine ⟨N, ?_⟩
        have h2pos : (0 : ℚ) < 2 ^ N := pow_pos (by norm_num) N
        have := mul_lt_mul_of_pos_right hN hlt
        rwa [div_mul_cancel₀ _ (ne_of_gt hlt), one_div, inv_pow, mul_comm,
          ← div_eq_mul_inv] at this
    use N
    intro j hj
    have hbA := toSeq_in_refineN a N j hj
    have hbR_own := toSeq_in_refineN a.refine N j hj
    have hcontain_l := a.refine_bounds_l
    have hcontain_r := a.refine_bounds_r
    have hbR : (AlgNum.refine^[N] a).l ≤ toSeq a.refine j ∧ toSeq a.refine j ≤ (AlgNum.refine^[N] a).r := by
      have : (AlgNum.refine^[N] a.refine) = (AlgNum.refine^[N] a).refine := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [this] at hbR_own
      constructor
      · exact le_trans (AlgNum.refine_bounds_l (AlgNum.refine^[N] a)) hbR_own.1
      · exact le_trans hbR_own.2 (AlgNum.refine_bounds_r (AlgNum.refine^[N] a))
    have hwidthN : (AlgNum.refine^[N] a).r - (AlgNum.refine^[N] a).l = (a.r - a.l) / 2 ^ N := refineN_width a N
    simp only [CauSeq.sub_apply]
    rw [abs_lt]
    constructor <;> nlinarith [hbA.1, hbA.2, hbR.1, hbR.2]
  )

instance : LT AlgNum where
  lt a b := a.r < b.l

theorem lt_toReal : ∀ (a b : AlgNum), a < b → a.toReal < b.toReal := by
  intros a b hlt
  have ha_bounds := toReal_bounds a
  have hb_bounds := toReal_bounds b
  have : (a.r : ℝ) < (b.l : ℝ) := Rat.cast_lt.mpr hlt
  linarith [ha_bounds.2, hb_bounds.1]

lemma refine_lt_toReal : ∀ a b : AlgNum, a.refine.toReal < b.refine.toReal → a.toReal < b.toReal := by
  intros a b h
  rw [refine_toReal a, refine_toReal b]
  exact h

end AlgebraicNumber
