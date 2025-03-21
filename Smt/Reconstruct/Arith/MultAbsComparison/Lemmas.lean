/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Regular

namespace Smt.Reconstruct.Arith

variable {α : Type}

variable [LinearOrderedCommRing α] -- satisfied by int, real, rat

theorem mul_cancel_a (a b c : α) : a * c = b * c → c ≠ 0 → a = b := by
  intros h1 h2
  have : (a - b) * c = 0 := by simp_all only [mul_eq_mul_right_iff, or_false, ne_eq, sub_self, zero_mul]
  have : a - b = 0 := (mul_eq_zero_iff_right h2).mp this
  simp_all only [mul_eq_mul_right_iff, or_false, ne_eq, sub_self, zero_mul]

theorem mul_eq_lt (a b c d : α) : 0 ≤ a → 0 ≤ c → d ≠ 0 → a * c = b * d → a < b → d < c := by
  intros ha hc hd h1 h2
  apply Classical.byContradiction
  intro abs
  push_neg at abs
  cases Decidable.eq_or_lt_of_le abs with
  | inl abs' =>
    rw [abs'] at h1
    have := mul_cancel_a a b d h1 hd
    rw [this] at h2
    exact (lt_self_iff_false b).mp h2
  | inr abs' =>
    have hb : 0 < b := lt_of_le_of_lt ha h2
    have : a * c < b * d := Right.mul_lt_mul_of_nonneg h2 abs' ha hc
    rw [h1] at this
    exact (lt_self_iff_false (b * d)).mp this

theorem mult_abs_1 : ∀ (x1 x2 y1 y2 : α), abs x1 ≤ abs x2 → abs y1 ≤ abs y2 → abs (x1 * y1) ≤ abs (x2 * y2) := by
  intro x1 x2 y1 y2 h1 h2
  rw [abs_mul x1 y1, abs_mul x2 y2]
  exact mul_le_mul h1 h2 (abs_nonneg y1) (abs_nonneg x2)

theorem mult_abs_2 : ∀ (x1 x2 y1 y2 : α), abs x1 < abs x2 → abs y1 ≤ abs y2 → y2 ≠ 0 → abs (x1 * y1) < abs (x2 * y2) := by
  intros x1 x2 y1 y2 h1 h2 h3
  rw [abs_mul x1 y1, abs_mul x2 y2]
  have := mul_le_mul (le_of_lt h1) h2 (abs_nonneg y1) (abs_nonneg x2)
  cases Decidable.eq_or_lt_of_le this with
  | inr hlt => exact hlt
  | inl heq =>
    have := mul_eq_lt |x1| |x2| |y1| |y2| (abs_nonneg x1) (abs_nonneg y1) (abs_ne_zero.mpr h3) heq h1
    exact lt_imp_lt_of_le_imp_le (fun _ => h2) this

theorem mult_abs_3 : ∀ (x1 x2 y1 y2 : α), abs x1 ≤ abs x2 → abs y1 < abs y2 → x2 ≠ 0 → abs (x1 * y1) < abs (x2 * y2) := by
  intros x1 x2 y1 y2 h1 h2 h3
  rw [abs_mul x1 y1, abs_mul x2 y2]
  have := mul_le_mul h1 (le_of_lt h2) (abs_nonneg y1) (abs_nonneg x2)
  cases Decidable.eq_or_lt_of_le this with
  | inr hlt => exact hlt
  | inl heq =>
    rw [mul_comm |x1| |y1|] at *
    rw [mul_comm |x2| |y2|] at *
    have := mul_eq_lt |y1| |y2| |x1| |x2| (abs_nonneg y1) (abs_nonneg x1) (abs_ne_zero.mpr h3) heq h2
    exact lt_imp_lt_of_le_imp_le (fun _ => h1) this

end Smt.Reconstruct.Arith
