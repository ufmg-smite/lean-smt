/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt.Reconstruct.Int.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/arith/rewrites

variable {t ts x xs : Int}

theorem plus_zero : ts + 0 + ss = ts + ss :=
  (Int.add_zero ts).symm ▸ rfl

theorem mul_one : ts * 1 * ss = ts * ss :=
  (_root_.Int.mul_one ts).symm ▸ rfl
theorem mul_zero : ts * 0 * ss = 0 :=
  (_root_.Int.mul_zero ts).symm ▸ (Int.zero_mul ss).symm ▸ rfl

theorem int_div_total {t s : Int} : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem int_div_total_one {t : Int} : t / 1 = t :=
  Int.ediv_one t
theorem int_div_total_zero {t : Int} : t / 0 = 0 :=
  Int.ediv_zero t

theorem int_mod_total {t s : Int} : s ≠ 0 → t % s = t % s :=
  const _ rfl
theorem int_mod_total_one {t : Int} : t % 1 = 0 :=
  Int.emod_one t
theorem int_mod_total_zero {t : Int} : t % 0 = t :=
  Int.emod_zero t

theorem neg_neg_one : -1 * (-1 * t) = t :=
  Int.neg_mul _ t ▸ (Int.one_mul t).symm ▸ Int.neg_mul_neg _ t ▸ (Int.one_mul t).symm ▸ rfl

-- Eliminations

theorem elim_uminus : -t = -1 * t :=
  Int.neg_eq_neg_one_mul t ▸ rfl
theorem elim_minus : t - s = t + -1 * s :=
  Int.neg_eq_neg_one_mul s ▸ Int.sub_eq_add_neg ▸ rfl
theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  propext Int.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Int.not_le.symm
theorem elim_int_gt {t s : Int} : (t > s) = (t ≥ s + 1) :=
  propext (Int.lt_iff_add_one_le s t)
theorem elim_int_lt {t s : Int} : (t < s) = (s ≥ t + 1) :=
  propext (Int.lt_iff_add_one_le t s)
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem leq_norm {t s : Int} : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨fun hts => Int.not_le.mpr (Int.add_le_add_right hts _),
           Int.not_lt.mp⟩

theorem geq_tighten {t s : Int} : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨Int.sub_nonneg_of_le, Int.le_of_sub_nonneg⟩

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext ⟨Int.neg_le_neg, Int.le_of_neg_le_neg⟩

theorem refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_lt : (t < t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩
theorem refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_gt : (t > t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩

theorem int_eq_elim {t s : Int} : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext ⟨(· ▸ And.intro (Int.le_refl t) (Int.le_refl t)), fun ⟨hst, hts⟩ => Int.le_antisymm hts hst⟩

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  Int.add_assoc xs w ys ▸ rfl

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  Int.mul_assoc xs w ys ▸ rfl

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  Int.add_assoc y z ws ▸ Int.mul_add x y (z + ws) ▸ rfl

theorem plus_cancel1 : ts + x + ss + (-1 * x) + rs = ts + ss + rs :=
  Int.neg_eq_neg_one_mul x ▸ Int.add_assoc ts x ss ▸ Int.add_assoc ts (x + ss) (-x) ▸
  Int.add_comm x ss ▸ (Int.add_neg_cancel_right ss x).symm ▸ rfl
theorem plus_cancel2 : ts + (-1 * x) + ss + x + rs = ts + ss + rs :=
  Int.neg_eq_neg_one_mul x ▸ Int.add_assoc ts (-x) ss ▸ Int.add_assoc ts (-x + ss) x ▸
  Int.add_comm (-x) ss ▸ (Int.neg_add_cancel_right ss x).symm ▸ rfl

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Int.Rewrite
