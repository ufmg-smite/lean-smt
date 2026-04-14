import CompPoly
import Smt.Reconstruct.Real.CAD.Sturm.Theorem
import Smt.Reconstruct.Real.CAD.Sturm.SeqDefs

open CompPoly

lemma lt_of_le_of_neq (a b : Rat) : a ≠ 0 → b ≠ 0 → a * b ≤ 0 → a * b < 0 := by
  intros h1 h2 h3
  by_contra! abs
  have : a * b = 0 := by linarith
  simp_all only [ne_eq, le_refl, mul_eq_zero, or_self]

lemma sgns_3 {a b c : Rat} : 0 < a * b → a * c ≤ 0 → b * c ≤ 0 := by
  intros h1 h2
  if ha: 0 < a then
    have hb : 0 < b := (Rat.mul_pos_iff_of_pos_left ha).mp h1
    have hc : c ≤ 0 := nonpos_of_mul_nonpos_right h2 ha
    nlinarith
  else
    if ha: a = 0 then
      rw [ha] at h1
      simp at h1
    else
      have ha : a < 0 := by grind
      have hb : b < 0 := (neg_iff_neg_of_mul_pos h1).mp ha
      have hc : 0 ≤ c := nonneg_of_mul_nonpos_right h2 ha
      nlinarith

lemma eval_comm_map (p : Polynomial Rat) (l : Rat) : (p.eval l) = (p.map ratToRealHom).eval (l : Real) := by
  simp [Polynomial.eval_eq_sum_range]

namespace AlgebraicNumber

-- The root of `p` in the interval `[l, r]`
structure Raw where
  p: CPolynomial Rat
  l: Rat
  r: Rat

namespace Raw

def wellDefined (a: Raw) : Prop :=
  let ⟨p, l, r⟩ := a
  ∃! x : Real, (toPolyReal p).eval x = 0 ∧ l ≤ x ∧ x ≤ r

-- This is also guaranteed by libpoly; this is necessary for `refine_wellDefined`.
def sgnDiff (a: Raw) : Prop :=
  (a.p.eval a.l) * (a.p.eval a.r) ≤ 0

lemma lr_wellDefined : ∀ a: Raw, a.wellDefined → a.l ≤ a.r := by
  rintro ⟨p, l, r⟩ ⟨x, ⟨hx, hxl, hxr⟩, hx_unique⟩
  have : (l : Real) ≤ r := Std.le_trans hxl hxr
  simp_all only [and_imp, Rat.cast_le]

def refine (a: Raw) : Raw :=
  let ⟨p, l, r⟩ := a
  let m := (l + r) / 2
  if p.eval l * p.eval m ≤ 0 then
    ⟨p, l, m⟩
  else
    ⟨p, m, r⟩

lemma refine_p (a : AlgebraicNumber.Raw) : a.refine.p = a.p := by
  simp [AlgebraicNumber.Raw.refine]
  split_ifs <;> rfl

lemma refine_bounds_l : ∀ (a : Raw), a.wellDefined → a.l ≤ a.refine.l := by
  intros a h
  have := lr_wellDefined a h
  simp [Raw.refine]
  split_ifs
  · linarith
  · linarith

lemma refine_bounds_r : ∀ (a : Raw), a.wellDefined → a.refine.r ≤ a.r := by
  intros a h
  have := lr_wellDefined a h
  simp [Raw.refine]
  split_ifs
  · linarith
  · linarith

lemma refine_wellDefined : ∀ a: Raw, a.wellDefined → a.sgnDiff → a.refine.wellDefined := by
  intros a ha hsgn_diff
  have hlr := lr_wellDefined a ha
  obtain ⟨p, l, r⟩ := a
  have hlr' : (l : Real) ≤ r := Rat.cast_le.mpr hlr
  obtain ⟨x, ⟨hx, hlx, hxr⟩, hx_unique⟩ := ha
  simp only [Raw.refine]
  split_ifs
  next hi =>
    rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly] at hi
    if hpl: p.toPoly.eval l = 0 then
      have hxl : l = x := by
        apply hx_unique
        constructor
        · unfold toPolyReal
          rw [<- eval_comm_map]
          exact Rat.cast_eq_zero.mpr hpl
        · grind
      use l
      simp only [le_refl, Rat.cast_le, true_and, and_imp]
      constructor
      · constructor
        · unfold toPolyReal
          rw [<- eval_comm_map]
          exact Rat.cast_eq_zero.mpr hpl
        · linarith
      · intros y hy1 hy2 hy3
        rw [hxl]
        apply hx_unique
        constructor
        · exact hy1
        · exact And.intro hy2 (by norm_num at hy3; linarith)
    else
      let m := (l + r) / 2
      if hpm: p.toPoly.eval m = 0 then
        use m
        simp only [Rat.cast_le, and_imp]
        constructor
        · constructor
          · unfold toPolyReal
            rw [<- eval_comm_map]
            exact Rat.cast_eq_zero.mpr hpm
          · grind
        · intros y hy1 hy2 hy3
          have : m = x := by
            apply hx_unique
            constructor
            · unfold toPolyReal
              rw [<- eval_comm_map]
              exact Rat.cast_eq_zero.mpr hpm
            · norm_cast
              grind
          rw [this]
          apply hx_unique
          constructor
          · exact hy1
          · exact And.intro hy2 (by norm_num at hy3; linarith)
      else
        have : p.toPoly.eval l * p.toPoly.eval m < 0 := lt_of_le_of_neq _ _ hpl hpm hi
        replace this : ((p.toPoly.eval l * p.toPoly.eval m) : Real) < (0 : Real) := by norm_cast
        rw [eval_comm_map, eval_comm_map] at this
        have hlm : (l : Real) ≤ m := by unfold m; norm_cast; linarith
        obtain ⟨R, hR1, hR2, hR3⟩ := exists_root_ioo_mul (p := toPolyReal p) hlm this
        have hRx : R = x := by
          refine hx_unique R ⟨hR3, ⟨le_of_lt hR1, ?_⟩⟩
          unfold m at hR2
          norm_num at hR2
          grind
        use R
        constructor
        · constructor
          · exact hR3
          · grind
        · intros y hy
          rw [hRx]
          refine hx_unique y ⟨hy.1, ⟨hy.2.1, ?_⟩⟩
          · norm_num at hy
            grind
  next hi =>
    push_neg at hi
    if hpr: p.toPoly.eval r = 0 then
      have hxr : r = x := by
        apply hx_unique
        constructor
        · unfold toPolyReal
          rw [<- eval_comm_map]
          exact Rat.cast_eq_zero.mpr hpr
        · grind
      use r
      simp only [le_refl, Rat.cast_le, and_imp]
      constructor
      · constructor
        · unfold toPolyReal
          rw [<- eval_comm_map]
          exact Rat.cast_eq_zero.mpr hpr
        · grind
      · intros y hy1 hy2 hy3
        rw [hxr]
        apply hx_unique
        constructor
        · exact hy1
        · exact And.intro (by norm_num at hy2; linarith) (by linarith)
    else
      have hm_neq0 : p.eval ((l + r) / 2) ≠ 0 := by
        intro abs
        rw [abs] at hi
        simp at hi
      have hsgn_diff' := sgns_3 hi hsgn_diff
      rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly] at hsgn_diff'
      have : p.toPoly.eval ((l + r) / 2) * p.toPoly.eval r ≠ 0 := by
        intro abs
        have : p.toPoly.eval ((l + r) / 2) = 0 ∨ p.toPoly.eval r = 0 := Rat.mul_eq_zero.mp abs
        cases this
        next H =>
          rw [CPolynomial.eval_toPoly] at hm_neq0
          exact hm_neq0 H
        next H => exact hpr H
      have mul_lt := Rat.lt_of_le_of_ne hsgn_diff' this
      have mul_lt_r : (toPolyReal p).eval (((l : Real) + r) / 2) * (toPolyReal p).eval (r : Real) < 0 := by
        unfold toPolyReal
        norm_cast
        rw [<- eval_comm_map, <- eval_comm_map]
        norm_cast
      obtain ⟨R, hR1, hR2, hR3⟩  := exists_root_ioo_mul (p := p.toPoly.map ratToRealHom) (by linarith) mul_lt_r
      have hRx : R = x := by
        refine hx_unique R ⟨?_, ⟨?_, ?_⟩⟩
        · unfold toPolyReal
          exact hR3
        · grind
        · grind
      use R
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hR3
      · norm_num
        grind
      · intros y hy
        norm_num at hy
        rw [hRx]
        refine hx_unique y ⟨hy.1, ⟨?_, ?_⟩⟩
        · grind
        · grind

lemma refine_sgnDiff : ∀ a: Raw, a.wellDefined → a.sgnDiff → a.refine.sgnDiff := by
  intros a ha hsgn_diff
  simp [Raw.refine]
  split_ifs
  next H =>
    simp [Raw.sgnDiff]
    assumption
  next H =>
    push_neg at H
    apply sgns_3 H hsgn_diff

lemma refine_width (a : Raw) : a.refine.r - a.refine.l = (a.r - a.l) / 2 := by
  obtain ⟨p, l, r⟩ := a
  simp [Raw.refine]
  split_ifs <;> ring

end Raw
