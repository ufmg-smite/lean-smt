/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Algebra.Order.Ring.Defs

namespace Smt.Reconstruct.Arith

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/arith/rewrites

open Function

variable {α : Type} [h : LinearOrderedRing α]

variable {t ts x xs : α}

theorem arith_plus_zero : ts + 0 + ss = ts + ss :=
  (add_zero ts).symm ▸ rfl
theorem arith_mul_one : ts * 1 * ss = ts * ss :=
  (mul_one ts).symm ▸ rfl
theorem arith_mul_zero : ts * 0 * ss = 0 :=
  (mul_zero ts).symm ▸ (zero_mul ss).symm ▸ rfl

theorem arith_int_div_one {t : Int} : t / 1 = t :=
  Int.ediv_one t

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
theorem arith_elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem arith_leq_norm {t s : Int} : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨(propext Int.not_le ▸ Int.lt_add_one_of_le ·),
           (Int.le_of_lt_add_one $ propext Int.not_le ▸ · )⟩

theorem arith_geq_tighten {t s : Int} : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

theorem arith_geq_norm: (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

theorem arith_refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem arith_refl_lt : (t < t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩
theorem arith_refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
theorem arith_refl_gt : (t > t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩

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

end Smt.Reconstruct.Arith
