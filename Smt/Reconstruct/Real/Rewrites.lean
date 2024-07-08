/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Basic

namespace Smt.Reconstruct.Real.Rewrite

open Function

theorem div_by_const_elim_1_pos {t : Real} : t / 1 = t * 1 :=
  div_eq_mul_one_div t 1 ▸ Eq.symm (@one_div_one Real _) ▸ rfl
theorem div_by_const_elim_1_neg {t : Real} : t / -1 = t * -1 :=
  div_eq_mul_one_div t (-1) ▸ div_neg (1 : Real) ▸ Eq.symm (@one_div_one Real _) ▸ rfl
theorem div_by_const_elim_num_pos {t c : Real} : t / c = t * (1 / c) :=
  div_eq_mul_one_div t c
theorem div_by_const_elim_num_neg {t c : Real} : t / -c = t * (-1 / c) :=
  div_eq_mul_one_div t (-c) ▸ div_neg (1 : Real) ▸ neg_div c 1 ▸ rfl
theorem div_by_const_elim_real_pos {t c₁ c₂ : Real} : t / (c₁ / c₂) = t * (c₂ / c₁) :=
  div_eq_mul_one_div t (c₁ / c₂) ▸ one_div_div c₁ c₂ ▸ rfl
theorem div_by_const_elim_real_neg {t c₁ c₂ : Real} : t / (-c₁ / c₂) = t * (-c₂ / c₁) :=
  div_eq_mul_one_div t (-c₁ / c₂) ▸ one_div_div (-c₁) c₂ ▸ div_neg c₂ ▸ neg_div c₁ c₂ ▸ rfl

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/arith/rewrites

variable {t ts x xs : Real}

theorem plus_zero : ts + 0 + ss = ts + ss :=
  (add_zero ts).symm ▸ rfl

theorem mul_one : ts * 1 * ss = ts * ss :=
  (_root_.mul_one ts).symm ▸ rfl
theorem mul_zero : ts * 0 * ss = 0 :=
  (MulZeroClass.mul_zero ts).symm ▸ (zero_mul ss).symm ▸ rfl

theorem div_total : s ≠ 0 → t / s = t / s :=
  const _ rfl

theorem neg_neg_one : -1 * (-1 * t) = t :=
  neg_mul _ t ▸ (one_mul t).symm ▸ neg_mul_neg _ t ▸ (one_mul t).symm ▸ rfl

-- Eliminations

theorem elim_uminus : -t = -1 * t :=
  neg_eq_neg_one_mul t ▸ rfl
theorem elim_minus : t - s = t + -1 * s :=
  neg_eq_neg_one_mul s ▸ sub_eq_add_neg _ s ▸ rfl
theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  propext not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext not_le.symm
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext (Iff.symm neg_le_neg_iff)

theorem refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem refl_lt : (t < t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩
theorem refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem refl_gt : (t > t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext (Iff.symm antisymm_iff)

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  add_assoc xs w ys ▸ rfl

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  mul_assoc xs w ys ▸ rfl

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  add_assoc y z ws ▸ mul_add x y (z + ws) ▸ rfl

theorem plus_cancel1 : ts + x + ss + (-1 * x) + rs = ts + ss + rs :=
  neg_eq_neg_one_mul x ▸ add_assoc ts x ss ▸ add_assoc ts (x + ss) (-x) ▸
  add_comm x ss ▸ (add_neg_cancel_right ss x).symm ▸ rfl
theorem plus_cancel2 : ts + (-1 * x) + ss + x + rs = ts + ss + rs :=
  neg_eq_neg_one_mul x ▸ add_assoc ts (-x) ss ▸ add_assoc ts (-x + ss) x ▸
  add_comm (-x) ss ▸ (neg_add_cancel_right ss x).symm ▸ rfl

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Real.Rewrite
