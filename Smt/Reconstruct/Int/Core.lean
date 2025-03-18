/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

namespace Int

protected def abs (x : Int) : Int :=
  if x < 0 then -x else x

def addN : List Int → Int
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, Int.add_assoc]
    all_goals (intro h; nomatch h)

def mulN : List Int → Int
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, Int.mul_assoc]
    all_goals (intro h; nomatch h)

@[simp]
protected theorem natCast_eq_zero {n : Nat} : (n : Int) = 0 ↔ n = 0 := by
  omega

protected theorem natCast_ne_zero {n : Nat} : (n : Int) ≠ 0 ↔ n ≠ 0 := by
  exact not_congr Int.natCast_eq_zero

protected theorem cast_pos' {x : Nat} : x ≠ 0 → (0 : Int) < x := by
  intro h
  have h' := Nat.zero_lt_of_ne_zero h
  exact Int.ofNat_pos.mpr h'

protected theorem gcd_def (i j : Int) : i.gcd j = i.natAbs.gcd j.natAbs :=
  rfl

protected theorem gcd_def' (i : Int) (j : Nat) : i.gcd (ofNat j) = i.natAbs.gcd j :=
  Int.gcd_def _ _

theorem gcd_eq_zero_iff {i j : Int} : gcd i j = 0 ↔ i = 0 ∧ j = 0 := by
  rw [gcd, Nat.gcd_eq_zero_iff, natAbs_eq_zero, natAbs_eq_zero]

theorem gcd_ne_zero_iff {i j : Int} : gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 := by
  constructor
  · intro h
    let tmp := not_congr gcd_eq_zero_iff |>.mp h
    if h_i : i = 0 then
      simp [h_i] at tmp
      exact Or.inr tmp
    else
      exact Or.inl h_i
  · intro h gcd_zero
    rw [gcd_eq_zero_iff] at gcd_zero
    simp [gcd_zero.1, gcd_zero.2] at h

protected theorem dvd_mul_left_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ k * j
| ⟨n, h⟩ => by
  rw [h]
  exists k * n
  rw [
    ← Int.mul_assoc k i n,
    Int.mul_comm k i,
    Int.mul_assoc i k n,
  ]

protected theorem natAbs_gcd_dvd {i : Int} {n : Nat} : ↑(i.natAbs.gcd n) ∣ i := by
  refine ofNat_dvd_left.mpr ?_
  exact Nat.gcd_dvd_left _ _

protected theorem natAbs_gcd_dvd' (i : Int) (n : Nat) : ↑(i.natAbs.gcd n) ∣ i :=
  Int.natAbs_gcd_dvd

protected theorem dvd_mul_right_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ j * k :=
  Int.mul_comm j k ▸ Int.dvd_mul_left_of_dvd k

theorem flatten_div_mul_eq_mul_div
  {i1 i2 i3 i4 j : Int}
  (j_pos : j ≠ 0)
  (j_dvd_i1 : j ∣ i1)
  (j_dvd_i4 : j ∣ i4)
: i1 / j * i2 = i3 * (i4 / j) → i1 * i2 = i3 * i4 := by
  intro h
  rw [← Int.mul_eq_mul_left_iff j_pos] at h
  conv at h =>
    lhs
    rw [← Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i1]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  conv at h =>
    rhs
    rw [← Int.mul_assoc]
    conv => lhs ; rw [Int.mul_comm]
    rw [Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i4]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  assumption

theorem not_lt_of_lt_rev {i j : Int} : i < j → ¬ j < i := by
  omega

theorem lt_of_le_of_ne {i j : Int} : i ≤ j → i ≠ j → i < j := by
  omega

@[simp]
theorem zero_le_natCast {n : Nat} : (0 : Int) ≤ n := by omega

@[simp]
theorem natCast_pos {n : Nat} : (0 : Int) < n ↔ 0 < n := by omega

@[simp]
theorem natCast_nonneg {n : Nat} : (0 : Int) ≤ n := by omega

theorem div_nonneg_iff_of_pos' {a b : Int} (h : 0 < b) : 0 ≤ a / b ↔ 0 ≤ a := by
  let tmp := @Int.div_nonneg_iff_of_pos a b h
  simp [GE.ge] at tmp
  exact tmp

variable {a b c : Int}

@[simp] protected
theorem neg_pos : 0 < -a ↔ a < 0 := ⟨Int.neg_of_neg_pos, Int.neg_pos_of_neg⟩

@[simp] protected
theorem neg_nonneg : 0 ≤ -a ↔ a ≤ 0 := ⟨Int.nonpos_of_neg_nonneg, Int.neg_nonneg_of_nonpos⟩

@[simp] protected
theorem neg_neg_iff_pos : -a < 0 ↔ 0 < a := ⟨Int.pos_of_neg_neg, Int.neg_neg_of_pos⟩

@[simp] protected
theorem neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
  ⟨Int.nonneg_of_neg_nonpos, Int.neg_nonpos_of_nonneg⟩

@[simp]
protected theorem sub_pos : 0 < a - b ↔ b < a := ⟨Int.lt_of_sub_pos, Int.sub_pos_of_lt⟩

@[simp]
protected theorem sub_nonneg : 0 ≤ a - b ↔ b ≤ a := ⟨Int.le_of_sub_nonneg, Int.sub_nonneg_of_le⟩

protected theorem le_rfl : a ≤ a := a.le_refl
protected theorem lt_or_lt_of_ne : a ≠ b → a < b ∨ b < a := Int.lt_or_gt_of_ne
protected theorem lt_or_le (a b : Int) : a < b ∨ b ≤ a := by
  rw [← Int.not_lt]
  apply Decidable.em
protected theorem le_or_lt (a b : Int) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem lt_asymm : a < b → ¬ b < a := by rw [Int.not_lt]; exact Int.le_of_lt
protected theorem le_of_eq (hab : a = b) : a ≤ b := by rw [hab]; exact Int.le_rfl
protected theorem ge_of_eq (hab : a = b) : b ≤ a := Int.le_of_eq hab.symm
protected theorem le_antisymm_iff {a b : Int} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨Int.le_of_eq h, Int.ge_of_eq h⟩, fun h ↦ Int.le_antisymm h.1 h.2⟩
protected theorem le_iff_eq_or_lt {a b : Int} : a ≤ b ↔ a = b ∨ a < b := by
  rw [Int.le_antisymm_iff, Int.lt_iff_le_not_le, ← and_or_left]
  simp [Decidable.em]
protected theorem le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := by rw [Int.le_iff_eq_or_lt, or_comm]

protected theorem div_gcd_nonneg_iff_of_pos
  {b : Nat} (b_pos : 0 < b)
: 0 ≤ a / (a.gcd b) ↔ 0 ≤ a := by
  let nz_den : (0 : Int) < a.gcd b := by
    apply Int.natCast_pos.mpr
    simp [Int.gcd]
    apply Nat.gcd_pos_of_pos_right _ b_pos
  exact Int.div_nonneg_iff_of_pos nz_den

protected theorem div_gcd_nonneg_iff_of_nz {b : Nat} (nz_b : b ≠ 0) : 0 ≤ a / (a.gcd b) ↔ 0 ≤ a :=
  Nat.pos_of_ne_zero nz_b |> Int.div_gcd_nonneg_iff_of_pos

@[simp]
theorem mul_nonneg_iff_of_pos_right (c_pos : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := ⟨
  by
    intro bc_nonneg
    apply Decidable.byContradiction
    intro h_b
    let h_b := Int.not_le.mp h_b

    apply Int.not_le.mpr (Int.mul_neg_of_neg_of_pos h_b c_pos)

    assumption
  ,
  by
    intro b_nonneg
    apply Int.mul_nonneg b_nonneg (Int.le_of_lt c_pos)
⟩

example (a b : Int) : ¬ a ≤ b → b < a := by exact fun a_1 => Int.lt_of_not_ge a_1


theorem mul_pos_iff_of_pos_right (c_pos : 0 < c) : 0 < b * c ↔ 0 < b := ⟨
  by
    intro bc_nonneg
    apply Decidable.byContradiction
    intro h_b'
    have h_b := Int.not_le.mp h_b'
    have := Int.not_lt.mp h_b'
    cases Int.le_iff_lt_or_eq.mp this with
    | inl n =>
        have := Int.not_le.mpr (Int.mul_neg_of_neg_of_pos n c_pos)
        have := Int.lt_of_not_ge this
        have := Int.lt_trans bc_nonneg this
        simp at this
    | inr n => rw [n] at bc_nonneg; simp at bc_nonneg
  ,
  by
    intro b_pos
    apply Int.mul_pos b_pos c_pos
⟩
end Int
