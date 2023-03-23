/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Std.Data.Int.Lemmas
import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Arith

scoped notation "const " c => fun _ => c

variable {xs w ys zs t x s r : Int}

-- Basic Rules

@[smt_simp] theorem arith_plus_zero : t + 0 + s = t + s :=
  t.add_zero.symm ▸ rfl

@[smt_simp] theorem arith_mul_one : t * 1 * s = t * s :=
  t.mul_one.symm ▸ rfl
@[smt_simp] theorem arith_mul_zero : t * 0 * s = 0 :=
  t.mul_zero.symm ▸ s.zero_mul.symm ▸ rfl

@[smt_simp] theorem arith_uminus_elim : -t = -1 * t :=
  t.neg_eq_neg_one_mul
@[smt_simp] theorem arith_neg_neg_one : -1 * (-1 * t) = t :=
  Int.mul_assoc (-1) (-1) t ▸ t.one_mul.symm ▸ rfl

-- Eliminations

@[smt_simp] theorem arith_elim_minus : t - s = t + -1 * s :=
  s.neg_eq_neg_one_mul ▸ rfl
@[smt_simp] theorem arith_elim_gt : (t > s) = ¬(t ≤ s) :=
  propext Int.not_le.symm
@[smt_simp] theorem arith_elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Int.not_le.symm
@[smt_simp] theorem arith_elim_leq : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext Int.not_lt.symm

@[smt_simp] theorem arith_geq_tighten : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

@[smt_simp] theorem arith_geq_norm: (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨Int.sub_nonneg_of_le, Int.le_of_sub_nonneg⟩

@[smt_simp] theorem arith_refl_leq : (t ≤ t) = True :=
  propext ⟨const trivial, const t.le_refl⟩
@[smt_simp] theorem arith_refl_lt : (t < t) = False :=
  propext ⟨t.lt_irrefl, False.elim⟩
@[smt_simp] theorem arith_refl_geq : (t ≥ t) = True :=
  propext ⟨const trivial, const t.le_refl⟩
@[smt_simp] theorem arith_refl_gt : (t > t) = False :=
  propext ⟨t.lt_irrefl, False.elim⟩

@[smt_simp] theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  Int.add_assoc xs w ys ▸ rfl

@[smt_simp] theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  Int.mul_assoc xs w ys ▸ rfl

@[smt_simp] theorem mult_dist : x * (y + z + w) = x * y + x * (z + w) :=
  Int.add_assoc y z w ▸ Int.mul_add x y (z + w) ▸ rfl

-- TEMPORARY

@[smt_simp] theorem arith_plus_cancel1 : t + x + s + (-1 * x) + r = t + s + r :=
  arith_uminus_elim ▸ Int.add_assoc t x s ▸ Int.add_assoc t (x + s) (-x) ▸
  Int.add_comm x s ▸ (Int.add_neg_cancel_right s x).symm ▸ rfl

@[smt_simp] theorem arith_plus_cancel2 : t + (-1 * x) + s + x + r = t + s + r :=
  arith_uminus_elim ▸ Int.add_assoc t (-x) s ▸ Int.add_assoc t (-x + s) x ▸
  Int.add_comm (-x) s ▸ (Int.neg_add_cancel_right s x).symm ▸ rfl

end Smt.Reconstruction.Rewrites.Arith
