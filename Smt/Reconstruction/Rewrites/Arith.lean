/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Algebra.Order.Ring.Defs
import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Arith

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/arith/rewrites

open Function

variable {α : Type} [LinearOrderedRing α]

variable {xs w ys zs t x s r : α}

@[smt_simp] theorem arith_plus_zero : t + 0 + s = t + s :=
  (add_zero t).symm ▸ rfl
@[smt_simp] theorem arith_mul_one : t * 1 * s = t * s :=
  (mul_one t).symm ▸ rfl
@[smt_simp] theorem arith_mul_zero : t * 0 * s = 0 :=
  (mul_zero t).symm ▸ (zero_mul s).symm ▸ rfl

@[smt_simp] theorem arith_int_div_one {t : Int} : t / 1 = t :=
  Int.ediv_one t

@[smt_simp] theorem arith_neg_neg_one : -1 * (-1 * t) = t :=
  neg_mul _ t ▸ (one_mul t).symm ▸ neg_mul_neg _ t ▸ (one_mul t).symm ▸ rfl

-- -- Eliminations

@[smt_simp] theorem arith_elim_uminus : -t = -1 * t :=
  neg_eq_neg_one_mul t ▸ rfl
@[smt_simp] theorem arith_elim_minus : t - s = t + -1 * s :=
  neg_eq_neg_one_mul s ▸ sub_eq_add_neg _ s ▸ rfl
@[smt_simp] theorem arith_elim_gt : (t > s) = ¬(t ≤ s) :=
  propext not_le.symm
@[smt_simp] theorem arith_elim_lt : (t < s) = ¬(t ≥ s) :=
  propext not_le.symm
@[smt_simp] theorem arith_elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

@[smt_simp] theorem arith_leq_norm {t s : Int}: (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨(propext Int.not_le ▸ Int.lt_add_one_of_le ·),
           (Int.le_of_lt_add_one $ propext Int.not_le ▸ · )⟩

@[smt_simp] theorem arith_geq_tighten {t s : Int} : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

@[smt_simp] theorem arith_geq_norm: (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨sub_nonneg_of_le, le_of_sub_nonneg⟩

@[smt_simp] theorem arith_refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
@[smt_simp] theorem arith_refl_lt : (t < t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩
@[smt_simp] theorem arith_refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (le_refl t)⟩
@[smt_simp] theorem arith_refl_gt : (t > t) = False :=
  propext ⟨(lt_irrefl t), False.elim⟩

@[smt_simp] theorem arith_plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  add_assoc xs w ys ▸ rfl

@[smt_simp] theorem arith_mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  mul_assoc xs w ys ▸ rfl

@[smt_simp] theorem arith_mult_dist : x * (y + z + w) = x * y + x * (z + w) :=
  add_assoc y z w ▸ mul_add x y (z + w) ▸ rfl

@[smt_simp] theorem arith_plus_cancel1 : t + x + s + (-1 * x) + r = t + s + r :=
  neg_eq_neg_one_mul x ▸ add_assoc t x s ▸ add_assoc t (x + s) (-x) ▸
  add_comm x s ▸ (add_neg_cancel_right s x).symm ▸ rfl

@[smt_simp] theorem arith_plus_cancel2 : t + (-1 * x) + s + x + r = t + s + r :=
  neg_eq_neg_one_mul x ▸ add_assoc t (-x) s ▸ add_assoc t (-x + s) x ▸
  add_comm (-x) s ▸ (neg_add_cancel_right s x).symm ▸ rfl

end Smt.Reconstruction.Rewrites.Arith
