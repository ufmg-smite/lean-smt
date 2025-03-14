/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Archimedean

namespace Smt.Reconstruct.Arith

open Function

theorem arith_div_by_const_elim_1_pos {t : Real} : t / 1 = t * 1 :=
  div_eq_mul_one_div t 1 ▸ Eq.symm (@one_div_one Real _) ▸ rfl
theorem arith_div_by_const_elim_1_neg {t : Real} : t / -1 = t * -1 :=
  div_eq_mul_one_div t (-1) ▸ div_neg (1 : Real) ▸ Eq.symm (@one_div_one Real _) ▸ rfl
theorem arith_div_by_const_elim_num_pos {t c : Real} : t / c = t * (1 / c) :=
  div_eq_mul_one_div t c
theorem arith_div_by_const_elim_num_neg {t c : Real} : t / -c = t * (-1 / c) :=
  div_eq_mul_one_div t (-c) ▸ div_neg (1 : Real) ▸ neg_div c 1 ▸ rfl
theorem arith_div_by_const_elim_real_pos {t c₁ c₂ : Real} : t / (c₁ / c₂) = t * (c₂ / c₁) :=
  div_eq_mul_one_div t (c₁ / c₂) ▸ one_div_div c₁ c₂ ▸ rfl
theorem arith_div_by_const_elim_real_neg {t c₁ c₂ : Real} : t / (-c₁ / c₂) = t * (-c₂ / c₁) :=
  div_eq_mul_one_div t (-c₁ / c₂) ▸ one_div_div (-c₁) c₂ ▸ div_neg c₂ ▸ neg_div c₁ c₂ ▸ rfl

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {α : Type} [h : LinearOrderedRing α]

variable {t ts x xs : α}

theorem arith_plus_zero : ts + 0 + ss = ts + ss :=
  (add_zero ts).symm ▸ rfl

theorem arith_mul_one : ts * 1 * ss = ts * ss :=
  (mul_one ts).symm ▸ rfl
theorem arith_mul_zero : ts * 0 * ss = 0 :=
  (mul_zero ts).symm ▸ (zero_mul ss).symm ▸ rfl

theorem arith_div_total {t s : Real} : s ≠ 0 → t / s = t / s :=
  const _ rfl

theorem arith_int_div_total {t s : Int} : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem arith_int_div_total_one {t : Int} : t / 1 = t :=
  Int.ediv_one t
theorem arith_int_div_total_zero {t : Int} : t / 0 = 0 :=
  Int.ediv_zero t

theorem arith_int_mod_total {t s : Int} : s ≠ 0 → t % s = t % s :=
  const _ rfl
theorem arith_int_mod_total_one {t : Int} : t % 1 = 0 :=
  Int.emod_one t
theorem arith_int_mod_total_zero {t : Int} : t % 0 = t :=
  Int.emod_zero t

theorem arith_neg_neg_one : -1 * (-1 * t) = t :=
  neg_mul _ t ▸ (one_mul t).symm ▸ neg_mul_neg _ t ▸ (one_mul t).symm ▸ rfl

-- Eliminations

theorem arith_elim_uminus : -t = -1 * t :=
  neg_eq_neg_one_mul t ▸ rfl
theorem arith_elim_minus : t - s = t + -1 * s :=
  neg_eq_neg_one_mul s ▸ sub_eq_add_neg _ s ▸ rfl
theorem arith_elim_gt : (t > s) = ¬(t ≤ s) :=
  propext not_le.symm
theorem arith_elim_lt : (t < s) = ¬(t ≥ s) :=
  propext not_le.symm
theorem arith_elim_int_gt {t s : Int} : (t > s) = (t ≥ s + 1) :=
  propext Int.lt_iff_add_one_le
theorem arith_elim_int_lt {t s : Int} : (t < s) = (s ≥ t + 1) :=
  propext Int.lt_iff_add_one_le
theorem arith_elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem arith_leq_norm {t s : Int} : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨(propext Int.not_le ▸ Int.lt_add_one_of_le ·),
           (Int.le_of_lt_add_one $ propext Int.not_le ▸ · )⟩

theorem arith_geq_tighten {t s : Int} : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

theorem arith_geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

theorem arith_geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext (Iff.symm neg_le_neg_iff)

theorem arith_refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem arith_refl_lt : (t < t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩
theorem arith_refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem arith_refl_gt : (t > t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩

theorem arith_real_eq_elim {t s : Real} : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext (Iff.symm antisymm_iff)
theorem arith_int_eq_elim {t s : Int} : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext (Iff.symm antisymm_iff)

theorem arith_plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  add_assoc xs w ys ▸ rfl

theorem arith_mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  mul_assoc xs w ys ▸ rfl

theorem arith_mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  add_assoc y z ws ▸ mul_add x y (z + ws) ▸ rfl

theorem arith_plus_cancel1 : ts + x + ss + (-1 * x) + rs = ts + ss + rs :=
  neg_eq_neg_one_mul x ▸ add_assoc ts x ss ▸ add_assoc ts (x + ss) (-x) ▸
  add_comm x ss ▸ (add_neg_cancel_right ss x).symm ▸ rfl
theorem arith_plus_cancel2 : ts + (-1 * x) + ss + x + rs = ts + ss + rs :=
  neg_eq_neg_one_mul x ▸ add_assoc ts (-x) ss ▸ add_assoc ts (-x + ss) x ▸
  add_comm (-x) ss ▸ (neg_add_cancel_right ss x).symm ▸ rfl

theorem arith_abs_elim : |x| = if x < 0 then -x else x :=
  if h : x < 0 then
    if_pos h ▸ abs_of_neg h
  else
    if_neg h ▸ abs_of_nonneg (le_of_not_lt h)

end Smt.Reconstruct.Arith
