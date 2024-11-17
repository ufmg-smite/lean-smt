/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Data.Rat

namespace Smt.Reconstruct.Rat.Rewrite

open Function

theorem div_by_const_elim {t c : Rat} : t / c = t * (1 / c) :=
  sorry

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t ts x xs : Rat}

theorem plus_zero : ts + 0 + ss = ts + ss :=
  sorry

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
  sorry
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  sorry
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  sorry

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  sorry

theorem refl_leq : (t ≤ t) = True :=
  sorry
theorem refl_lt : (t < t) = False :=
  sorry
theorem refl_geq : (t ≥ t) = True :=
  sorry
theorem refl_gt : (t > t) = False :=
  sorry

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  sorry

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  sorry

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  sorry

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  sorry

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Rat.Rewrite
