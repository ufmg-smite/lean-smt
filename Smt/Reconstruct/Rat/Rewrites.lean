/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Batteries.Data.Rat
import Smt.Reconstruct.Rat.Lemmas

namespace Smt.Reconstruct.Rat.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t ts x xs : Rat}

theorem plus_zero : ts + 0 + ss = ts + ss := by simp


theorem mul_one : ts * 1 * ss = ts * ss :=
  (_root_.Rat.mul_one ts).symm ▸ rfl
theorem mul_zero : ts * 0 * ss = 0 :=
  (_root_.Rat.mul_zero ts).symm ▸ (Rat.zero_mul ss).symm ▸ rfl

theorem div_total : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem div_total_zero : x / 0 = 0 :=
  Rat.div_def x 0 ▸ Rat.inv_zero.symm ▸ Rat.mul_zero x

-- Eliminations
theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  propext (Rat.not_le _).symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext (Rat.not_le _).symm
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) := by
  rw [←elim_leq, ←elim_leq, Rat.le_iff_sub_nonneg _ _]

#check Rat.neg_neg

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext ⟨Rat.neg_le_neg,
          fun h => by
          have := Rat.neg_le_neg h
          simp [Rat.neg_neg] at this
          assumption⟩

theorem refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (Rat.le_refl t)⟩
theorem refl_lt : (t < t) = False :=
  propext ⟨(Rat.lt_irrefl t), False.elim⟩
theorem refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (Rat.le_refl t)⟩
theorem refl_gt : (t > t) = False :=
  propext ⟨(Rat.lt_irrefl t), False.elim⟩

example (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  apply And.comm

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) := by
  apply propext
  rw [←elim_leq, And.comm]
  exact Rat.le_antisymm_iff _ _

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs := by
  simp [Rat.add_assoc]

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs := by
  simp [Rat.mul_assoc]

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) := by
  simp [Rat.mul_add, Rat.add_assoc]

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Rat.Rewrite
