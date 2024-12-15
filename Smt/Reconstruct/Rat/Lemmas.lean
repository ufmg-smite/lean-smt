/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

import Batteries.Data.Rat
import Smt.Reconstruct.Rat.Core

theorem Rat.add_comm (a b : Rat) : a + b = b + a := by
  simp [Rat.add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

theorem Rat.neg_self_add (c : Rat) : -c + c = 0 := by
  simp [Rat.add_def]
  exact Int.add_left_neg _

theorem Rat.add_neg_self (c : Rat) : c + (-c) = 0 := by
  rw [Rat.add_comm]
  exact Rat.neg_self_add c

theorem Rat.neg_add (a b : Rat) : -(a + b) = -a - b := by
  rw [Rat.add_def, Rat.sub_def, Rat.neg_normalize, Int.neg_add, Int.sub_eq_add_neg]
  simp

theorem Rat.zero_add (a : Rat) : 0 + a = a := by
  rw [Rat.add_comm]
  exact Rat.add_zero a

theorem add_sub_add_left_eq_sub (a b c : Rat) : c + a - (c + b) = a - b := by
  rw [ Rat.sub_eq_add_neg,
       Rat.add_assoc c a (-(c + b)),
       Rat.add_comm a (-(c + b)),
       <- Rat.add_assoc c (-(c + b)) a,
       Rat.neg_add,
       Rat.sub_eq_add_neg,
       <- Rat.add_assoc c (-c) (-b),
       Rat.add_neg_self,
       Rat.zero_add,
       Rat.add_comm,
       Rat.sub_eq_add_neg
    ]

theorem mk_eq_divInt (num den nz c) : Rat.mk' num den nz c = Rat.divInt num (den : Nat) := by
  simp [Rat.mk_eq_mkRat]

def numDenCasesOn'' {C : Rat → Sort} (a : Rat)
    (H : ∀ (n : Int) (d : Nat) (nz red), C (Rat.mk' n d nz red)) : C a :=
  Rat.numDenCasesOn a fun n d h h' ↦ by rw [← mk_eq_divInt _ _ ((Ne.symm (Nat.ne_of_lt h))) h']; exact H n d ((Ne.symm (Nat.ne_of_lt h))) _

theorem le_rfl (a : Int) : a ≤ a := a.le_refl
theorem lt_or_lt_of_ne (a b : Int) : a ≠ b → a < b ∨ b < a := Int.lt_or_gt_of_ne
theorem lt_or_le (a b : Int) : a < b ∨ b ≤ a := by rw [← Int.not_lt]; exact Classical.em _
theorem le_or_lt (a b : Int) : a ≤ b ∨ b < a := Or.comm.1 (lt_or_le b a)
theorem lt_asymm (a b : Int) : a < b → ¬ b < a := by rw [Int.not_lt]; exact Int.le_of_lt
theorem le_of_eq (a b : Int) (hab : a = b) : a ≤ b := by rw [hab]; exact le_rfl b
theorem ge_of_eq (a b : Int) (hab : a = b) : b ≤ a := by rw [hab]; exact le_rfl b
theorem le_antisymm_iff (a b : Int) : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨by rw [h]; exact le_rfl b, by rw [h]; exact le_rfl b⟩, fun h ↦ Int.le_antisymm h.1 h.2⟩
theorem le_iff_eq_or_lt (a b : Int) : a ≤ b ↔ a = b ∨ a < b := by
  rw [le_antisymm_iff, Int.lt_iff_le_not_le, ← and_or_left]; simp [Classical.em]
theorem le_iff_lt_or_eq (a b : Int) : a ≤ b ↔ a < b ∨ a = b := by rw [le_iff_eq_or_lt, or_comm]

theorem num_nonneg (q : Rat) : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [le_iff_lt_or_eq, Rat.instLE, Rat.blt, Int.not_lt];
  intros h1 _ _
  exact h1

theorem num_pos (q : Rat) : 0 < q.num ↔ 0 < q := by
  simp [Rat.instLT, Rat.blt]

theorem natCast_pos {n : Nat} : (0 : Int) < n ↔ 0 < n := by omega

theorem natCast_nonneg (n : Nat) : 0 ≤ (n : Int) := Int.ofNat_zero_le n

theorem zero_of_num_zero {q : Rat} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.divInt_self.symm

theorem zero_iff_num_zero {q : Rat} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

theorem Rat.mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

theorem zero_sub (q : Rat) : 0 - q = -q := by
  rw [Rat.sub_def]; simp; rw [<- Rat.neg_normalize, Rat.normalize_self]

theorem Left.nonneg_neg_iff (a : Int) : 0 ≤ -a ↔ a ≤ 0 := by
  constructor
  · intro h; exact Int.nonpos_of_neg_nonneg h
  · intro h; exact Int.neg_nonneg_of_nonpos h

theorem sub_nonneg (a b : Int) : 0 ≤ a - b ↔ b ≤ a := ⟨Int.le_of_sub_nonneg, Int.sub_nonneg_of_le⟩

theorem push_neg {p q : Prop} : ¬ (p ∧ q) → p → ¬ q := fun h hp hq => h (And.intro hp hq)

theorem double_neg : (¬ (¬ p)) -> p :=
  match Classical.em p with
  | Or.inl hp => fun _ => hp
  | Or.inr hnp => fun hnnp => False.elim (hnnp hnp)

theorem le_iff_sub_nonneg (a b : Rat) : a ≤ b ↔ 0 ≤ b - a :=
  numDenCasesOn'' (C := fun r => r ≤ b ↔ 0 ≤ b - r) a fun na da ha hared =>
    numDenCasesOn'' (C := fun r => Rat.mk' na da ha hared ≤ r ↔ 0 ≤ r - Rat.mk' na da ha hared) b fun nb db hb hbred => by
      change Rat.blt _ _ = false ↔ _
      unfold Rat.blt
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, Int.not_lt, ite_eq_left_iff, not_and, Int.not_le, ← num_nonneg]
      by_cases h : nb < 0 ∧ 0 ≤ na
      · simp [h]
        rw [Rat.sub_def];
        simp only [false_iff, Int.not_le, reduceCtorEq]
        simp only [Rat.normalize_eq]
        apply Int.ediv_neg'
        · refine Int.sub_neg_of_lt ?_
          apply Int.lt_of_lt_of_le
          · apply Int.mul_neg_of_neg_of_pos h.1
            rwa [natCast_pos, Nat.pos_iff_ne_zero]
          · apply Int.mul_nonneg h.2 (natCast_nonneg _)
        · simp only [natCast_pos, Nat.pos_iff_ne_zero]
          exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)
      · simp [h]
        by_cases h' : nb = 0
        · simp [h', Rat.mk'_zero, zero_sub, Rat.neg_num, Left.nonneg_neg_iff]
        · simp [h']
          simp only [Rat.sub_def, Rat.normalize_eq]
          refine ⟨fun H => ?_, fun H _ => ?_⟩
          · refine Int.ediv_nonneg ?_ (natCast_nonneg _)
            rw [sub_nonneg]
            obtain hb | hb := lt_or_lt_of_ne _ _ h'
            · apply H
              intro H'
              have abs := Int.lt_trans H' hb
              simp at abs
            · obtain ha|ha := le_or_lt na 0
              · apply Int.le_trans <| Int.mul_nonpos_of_nonpos_of_nonneg ha (natCast_nonneg _)
                exact Int.mul_nonneg (Int.le_of_lt hb) (natCast_nonneg _)
              · exact H (fun _ => ha)
          · rw [← sub_nonneg]
            apply double_neg
            intro H'
            have H' := Int.not_le.mp H'
            suffices  ¬ 0 ≤ (nb * ↑da - na * ↑db) / ↑((nb * ↑da - na * ↑db).natAbs.gcd (db * da))  by exact this H
            rw [Int.not_le]
            apply Int.ediv_neg' H'
            simp only [natCast_pos, Nat.pos_iff_ne_zero]
            exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)

theorem add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b := by
  rw [le_iff_sub_nonneg, add_sub_add_left_eq_sub, ← le_iff_sub_nonneg]

theorem ne_of_gt {a b : Int} (h : b < a) : a ≠ b := by
  intro h1
  rw [h1] at h
  simp at h

theorem mul_le_mul_iff_of_pos_right {a b c : Int} (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  ⟨(Int.le_of_mul_le_mul_right · ha), (Int.mul_le_mul_of_nonneg_right · (Int.le_of_lt ha))⟩

theorem mul_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a := by
  simpa using (mul_le_mul_iff_of_pos_right hb : 0 * b ≤ a * b ↔ 0 ≤ a)

@[simp] theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ Rat.divInt a b ↔ 0 ≤ a := by
  cases hab : Rat.divInt a b with
  | mk' n d hd hnd =>
      rw [Rat.mk'_eq_divInt, Rat.divInt_eq_iff (ne_of_gt hb) (mod_cast hd)] at hab
      rw [← num_nonneg, ← mul_nonneg_iff_of_pos_right hb, ← hab,
         mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

theorem le_add_neg_iff_add_le {a b c : Int} : c ≤ a + (-b) ↔ c + b ≤ a := by
  constructor
  · intro h; exact Int.add_le_of_le_sub_right h
  · intro h; rw [<- Int.sub_eq_add_neg]; exact Int.le_sub_right_of_add_le h

theorem divInt_le_divInt {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d) :
    Rat.divInt a b ≤ Rat.divInt c d ↔ a * d ≤ c * b := by
  rw [le_iff_sub_nonneg, ← sub_nonneg]
  simp only [Rat.sub_eq_add_neg, Rat.neg_divInt, ne_eq, ne_of_gt d0, not_false_eq_true, ne_of_gt b0,
    Rat.divInt_add_divInt, Int.neg_mul, Int.mul_pos d0 b0, divInt_nonneg_iff_of_pos_right,
    le_add_neg_iff_add_le, Int.zero_add, sub_nonneg]

-- Look at Mathlib/Algebra/Order/Ring/Unbundled/Rat.lean
private theorem Rat.mul_lt_mul_left {c x y : Rat} (hc : c > 0) : (c * x < c * y) = (x < y) := by
  apply propext
  exact
    numDenCasesOn' (C := fun r => c * r < c * y ↔ r < y) x fun n₁ d₁ h₁ =>
    numDenCasesOn' (C := fun r => c * (Rat.divInt n₁ d₁) < c * r ↔ (Rat.divInt n₁ d₁) < r) y fun n₂ d₂ h₂ =>
    numDenCasesOn' (C := fun r => r * (Rat.divInt n₁ d₁) < r * (Rat.divInt n₂ d₂) ↔ (Rat.divInt n₁ d₁) < (Rat.divInt n₂ d₂)) c fun n₃ d₃ h₃ => by admit

theorem tt {x : Nat} : x ≠ 0 → (0 : Int) < x := by
  intro h
  have h' := Nat.zero_lt_of_ne_zero h
  exact natCast_pos.mpr h'

theorem Rat.le_of_lt {c : Rat} : 0 < c → 0 ≤ c := by
  intro h
  simp [Rat.instLE]
  simp [Rat.instLT] at h
  simp [Rat.blt] at *
  constructor
  · exact lt_asymm 0 c.num h
  · intro _ h2 _; exact h2 h

private theorem Rat.mul_le_mul_left {c x y : Rat} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  apply propext
  exact
    numDenCasesOn' (C := fun r => c * r ≤ c * y ↔ r ≤ y) x fun n₁ d₁ h₁ =>
    numDenCasesOn' (C := fun r => c * (Rat.divInt n₁ d₁) ≤ c * r ↔ (Rat.divInt n₁ d₁) ≤ r) y fun n₂ d₂ h₂ => by
      cases c_def : c with
      | mk' nc dc dc_nz _ =>
        rw [<- c_def, <- divInt_self c]
        have foo : (c.den : Int) ≠ (0 : Int) := by rw [c_def]; exact Int.ofNat_ne_zero.mpr dc_nz
        have bar : (d₂ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₂
        have baz : (d₁ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₁
        rw [Rat.divInt_mul_divInt _ _ foo bar, Rat.divInt_mul_divInt _ _ foo baz]
        have c_den_pos : (0 : Int) < c.den := tt fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := tt h₁
        have d2_pos : (0 : Int) < d₂ := tt h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [divInt_le_divInt den_pos1 den_pos2]
        rw [divInt_le_divInt d1_pos d2_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h
          have c_num_pos : 0 < c.num := (num_pos c).mpr hc
          have h' := Int.le_of_mul_le_mul_left h c_num_pos
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc] at h'
          exact Int.le_of_mul_le_mul_left h' c_den_pos
        · intro h
          have : 0 ≤ c.num := (num_nonneg c).mpr (Rat.le_of_lt hc)
          refine Int.mul_le_mul_of_nonneg_left ?_ this
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc]
          exact Int.mul_le_mul_of_nonneg_left h (natCast_nonneg c.den)

private theorem Rat.mul_eq_zero_left {x y : Rat} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  sorry

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Rat

variable {a b c d : Rat}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  sorry

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  sorry

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rw [h₂, Rat.add_comm, Rat.add_comm b d]
  exact add_le_add_left.mpr h₁

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rw [h₁, Rat.add_comm b c, Rat.add_comm b d]
  exact sum_ub₃ h₂ rfl

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rw [h₁]
  exact add_le_add_left.mpr h₂

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  rw [h₁, h₂]
  simp [Rat.instLE, Rat.blt]
  constructor
  · intros h₃ h₄; exact Lean.Omega.Int.le_lt_asymm h₄ h₃
  · intros h₃ h₄; rw [h₃] at h₄; simp at h₄

theorem neg_lt_neg (h : a < b) : -a > -b := by
  sorry

theorem neg_le_neg (h : a ≤ b) : -a ≥ -b := by
  sorry

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.ceil - 1 := by
  sorry

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.floor + 1 := by
  sorry

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  sorry

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  sorry

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  sorry

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  sorry

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  sorry

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  sorry

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  sorry

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  sorry

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  apply propext
  constructor
  · intro h; rw [h]; simp [Rat.sub_def]
  · intro h; admit

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  apply propext
  exact le_iff_sub_nonneg b a

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  sorry

theorem lt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by admit

theorem ge_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  sorry

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  sorry

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  sorry

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  sorry

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  sorry

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  sorry

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  sorry

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  sorry

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  sorry

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  sorry

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  sorry

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  sorry

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  sorry

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat
