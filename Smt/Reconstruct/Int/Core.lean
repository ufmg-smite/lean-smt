/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

namespace Int

protected def abs (x : Int) : Int :=
  if x < 0 then -x else x

theorem abs_eq (hb : 0 ≤ b) : a.abs = b ↔ a = b ∨ a = -b := by
  unfold Int.abs
  omega

theorem abs_nonneg (x : Int) : 0 ≤ x.abs := by
  unfold Int.abs
  omega

theorem abs_of_nonpos (h : a ≤ 0) : a.abs = -a := by
  unfold Int.abs
  omega

theorem abs_of_nonneg {a : Int} (h : 0 ≤ a) : a.abs = a := by
  unfold Int.abs
  omega

theorem abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq (Int.mul_nonneg (Int.abs_nonneg a) (Int.abs_nonneg b))]
  rcases Int.le_total a 0 with ha | ha <;> rcases Int.le_total b 0 with hb | hb <;>
    simp only [Int.abs_of_nonpos, Int.abs_of_nonneg, true_or, or_true, eq_self_iff_true, Int.neg_mul,
      Int.mul_neg, Int.neg_neg, *]

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

@[simp] theorem addN_cons_append : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, Int.add_zero]

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

@[simp] theorem mulN_cons_append : mulN (x :: xs) = x * mulN xs := by
  cases xs <;> simp only [mulN, Int.mul_one]

protected theorem cast_pos' {x : Nat} : x ≠ 0 → (0 : Int) < x := by
  intro h
  have h' := Nat.zero_lt_of_ne_zero h
  exact Int.natCast_pos.mpr h'

protected theorem gcd_def (i j : Int) : i.gcd j = i.natAbs.gcd j.natAbs :=
  rfl

protected theorem gcd_def' (i : Int) (j : Nat) : i.gcd (ofNat j) = i.natAbs.gcd j :=
  Int.gcd_def _ _

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

theorem div_nonneg_iff_of_pos' {a b : Int} (h : 0 < b) : 0 ≤ a / b ↔ 0 ≤ a := by
  let tmp := @Int.ediv_nonneg_iff_of_pos a b h
  simp [GE.ge] at tmp
  exact tmp

variable {a b c : Int}

protected theorem le_or_lt (a b : Int) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem div_gcd_nonneg_iff_of_pos
  {b : Nat} (b_pos : 0 < b)
: 0 ≤ a / (a.gcd b) ↔ 0 ≤ a := by
  let nz_den : (0 : Int) < a.gcd b := by
    apply Int.natCast_pos.mpr
    simp [gcd, natAbs_natCast, Nat.gcd_pos_iff, natAbs_pos, ne_eq, b_pos]
  exact Int.ediv_nonneg_iff_of_pos nz_den

protected theorem div_gcd_nonneg_iff_of_nz {b : Nat} (nz_b : b ≠ 0) : 0 ≤ a / (a.gcd b) ↔ 0 ≤ a :=
  Nat.pos_of_ne_zero nz_b |> Int.div_gcd_nonneg_iff_of_pos

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
