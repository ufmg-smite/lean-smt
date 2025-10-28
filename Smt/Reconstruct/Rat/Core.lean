/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion, Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruct.Int.Core

namespace Rat

variable (x y a b c q : Rat)

protected def abs (x : Rat) := if x < 0 then -x else x

instance : NatPow Rat where
  pow := Rat.pow

def ceil' (r : Rat) := -((-r).floor)

theorem divInt_num (q : Rat) : (q.num /. q.den).num = q.num := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_num'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).num = n := by
  simp [mkRat, nz_d, normalize, reduced]

theorem divInt_den (q : Rat) : (q.num /. q.den).den = q.den := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_den'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).den = d := by
  simp [mkRat, nz_d, normalize, reduced]

protected theorem normalize_den_ne_zero
: ∀ {d : Int} {n : Nat}, (h : n ≠ 0) → (normalize d n h).den ≠ 0 := by
  intro d n nz
  simp only [Rat.normalize_eq, ne_eq]
  intro h
  apply nz
  rw [← Nat.zero_mul (d.natAbs.gcd n)]
  apply Nat.div_eq_iff_eq_mul_left _ _ |>.mp
  · assumption
  · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero nz)
  · exact Nat.gcd_dvd_right _ _

protected theorem eq_mkRat : ∀ a : Rat, a = mkRat a.num a.den := fun a => by
  simp [Rat.mkRat_def, a.den_nz, Rat.normalize_eq, a.reduced]

@[simp]
theorem mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by
  congr
  apply Nat.coprime_zero_left d |>.mp w

theorem eq_iff_mul_eq_mul {p q : Rat} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_divInt_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

protected theorem lt_iff_blt {x y : Rat} : x < y ↔ x.blt y := by
  simp only [LT.lt]

protected theorem le_iff_blt {x y : Rat} : x ≤ y ↔ ¬ y.blt x := by
  simp [LE.le]

protected theorem le_antisymm' {a b : Rat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_sub_nonneg] at hab hba
  rw [Rat.sub_eq_add_neg] at hba
  rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hab
  have := congrArg (· + b) (Rat.nonneg_antisymm hba hab)
  simpa only [Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add, Rat.add_zero] using this

protected theorem lt_asymm {x y : Rat} : x < y → ¬ y < x := by
  rewrite [Rat.not_lt]
  exact Rat.le_of_lt

protected theorem mul_eq_zero_iff : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · simp only [Rat.mul_def, Rat.normalize_eq_zero]
    intro h
    cases Int.mul_eq_zero.mp h
    · apply Or.inl
      rw [Rat.eq_mkRat a, Rat.mkRat_eq_zero]
      assumption
      exact a.den_nz
    · apply Or.inr
      rw [Rat.eq_mkRat b, Rat.mkRat_eq_zero]
      assumption
      exact b.den_nz
  · intro
    | .inl h => simp only [h, Rat.zero_mul]
    | .inr h => simp only [h, Rat.mul_zero]

protected theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp only [not_congr (Rat.mul_eq_zero_iff a b), not_or, ne_eq]

@[simp]
theorem neg_neg : - -q = q := by
  rewrite [← Rat.mkRat_self q, Rat.neg_mkRat, Rat.neg_mkRat]
  simp

theorem num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := not_congr num_eq_zero

theorem nonneg_iff_sub_nonpos : 0 ≤ q ↔ -q ≤ 0 := by
  rw [← num_nonneg]
  conv => rhs; simp [LE.le, Rat.blt]
  rfl

theorem nonneg_sub_iff_nonpos : 0 ≤ -q ↔ q ≤ 0 := by
  simp [nonneg_iff_sub_nonpos, Rat.neg_neg]

@[simp]
theorem num_nonpos : q.num ≤ 0 ↔ q ≤ 0 := by
  conv => lhs ; rw [← Int.neg_nonneg]
  simp only [Rat.neg_num q ▸ @num_nonneg (-q)]
  conv => rhs ; rw [← nonneg_sub_iff_nonpos]

theorem not_nonpos : ¬ q ≤ 0 ↔ 0 < q := by
  simp [Rat.lt_iff_blt, Rat.blt]
  rw [← num_nonpos]
  exact Int.not_le

@[simp]
theorem num_pos : 0 < q.num ↔ 0 < q := by
  let tmp := not_congr (num_nonpos (q := q))
  rw [Int.not_le] at tmp
  simp [tmp, Rat.not_nonpos]

theorem pos_iff_neg_nonpos : 0 < q ↔ -q < 0 := by
  rw [← num_pos]
  conv => rhs ; simp [Rat.lt_iff_blt] ; unfold Rat.blt ; simp
  constructor <;> intro h
  · apply Or.inl
    exact (num_pos q).mp h
  · let h : 0 < q := by
      cases h
      case inl h => exact h
      case inr h => exact h.2.2
    apply (num_pos q).mpr h

@[simp]
theorem num_neg : q.num < 0 ↔ q < 0 := by
  let tmp := @num_pos (-q)
  simp [Rat.neg_num q] at tmp
  rw [tmp]
  apply Rat.neg_neg q ▸ Rat.pos_iff_neg_nonpos (q := -q)

@[simp]
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

@[simp]
protected theorem sub_self : x - x = 0 :=
  numDenCasesOn' x fun nx dx h_dx => by
    rw [Rat.divInt_sub_divInt _ _ (Int.natCast_ne_zero.mpr h_dx) (Int.natCast_ne_zero.mpr h_dx)]
    simp

protected theorem add_neg_self : x + -x = 0 :=
  Rat.sub_eq_add_neg x x ▸ Rat.sub_self x

protected theorem eq_neg_of_add_eq_zero_left : x + y = 0 → x = - y :=
  numDenCasesOn'' x fun nx dx h_dx h_dx_red =>
  numDenCasesOn'' y fun ny dy h_dy h_dy_red => by
    simp only [Rat.add_def, Neg.neg]
    simp only [Rat.neg, normalize_eq_zero]
    simp only [eq_iff_mul_eq_mul, ← Int.neg_mul_eq_neg_mul]
    intro h
    apply Int.eq_neg_of_eq_neg
    exact Int.neg_eq_of_add_eq_zero h |>.symm

protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a := by
  rw [Rat.le_iff_sub_nonneg b a]

theorem divInt_pos_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 < a /. b ↔ 0 < a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_divInt_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [ ← Rat.num_pos, <- Int.mul_pos_iff_of_pos_right hb, <- hab,
       Int.mul_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

theorem divInt_neg_iff_of_neg_right {a b : Int} (hb : 0 < b) : 0 > a /. b ↔ 0 > a := by
  have f : ¬ (0 ≤ a /. b) ↔ ¬ (0 ≤ a) := not_congr (divInt_nonneg_iff_of_pos_right hb)
  rw [Int.not_le, Rat.not_le] at f
  exact f

protected theorem divInt_le_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [Rat.sub_eq_add_neg, Rat.neg_divInt]
  rw [Rat.divInt_add_divInt]
  simp only [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos d0 b0), Int.neg_mul]
  rw [← Int.sub_nonneg (a := c * b)]
  rw [← Int.sub_eq_add_neg]
  · apply Int.lt_iff_le_and_ne.mp d0 |>.2 |>.symm
  · apply Int.lt_iff_le_and_ne.mp b0 |>.2 |>.symm

theorem cast_lt1 {a b : Int} : Rat.ofInt a < Rat.ofInt b -> a < b := by
  intro h
  simp [Rat.instLT, Rat.ofInt] at h
  simp [Rat.blt] at h
  cases h with
  | inl h =>
    let ⟨h1, h2⟩ := h
    exact Int.lt_of_lt_of_le h1 h2
  | inr h =>
    cases Classical.em (a = 0) with
    | inl ha => simp [ha] at h; exact lt_of_eq_of_lt ha h
    | inr ha =>
      simp [ha] at h
      exact h.2

theorem cast_lt2 {a b : Int} : a < b → Rat.ofInt a < Rat.ofInt b := by
  intro h
  simp only [instLT, ofInt, mk_den_one]
  simp [Rat.blt]
  cases Classical.em (a = 0) with
  | inl ha => simp [ha]; rw [ha] at h; exact h
  | inr ha =>
      simp only [ha, ↓reduceIte]
      right
      constructor
      · omega
      · exact h

theorem cast_lt {a b : Int} : a < b ↔ Rat.ofInt a < Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_le1 {a b : Int} : Rat.ofInt a ≤ Rat.ofInt b -> a ≤ b := by
  intro h
  simp only [instLE, ofInt, mk_den_one] at h
  simp [Rat.blt] at h
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb] at h
    rw [hb]
    exact h
  | inr hb =>
    simp [hb] at h
    let ⟨h1, h2⟩ := h
    cases Classical.em (a ≤ b) with
    | inl hab => exact hab
    | inr hab =>
      have : ¬ a ≤ b → ¬ (b ≤ 0 ∨ 0 < a) := fun a_1 a => hab (h2 a)
      have := this hab
      rw [not_or] at this
      let ⟨h3, h4⟩ := this
      rw [Int.not_le] at h3
      rw [Int.not_lt] at h4
      have := Int.lt_of_le_of_lt h4 h3
      exact Int.le_of_lt this

theorem cast_le2 {a b : Int} : a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by
  intro h
  simp [Rat.instLE, Rat.ofInt]
  simp [Rat.blt]
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb]
    rw [hb] at h
    exact h
  | inr hb =>
    simp [hb]
    constructor <;> omega

theorem cast_le {a b : Int} : a ≤ b ↔ Rat.ofInt a ≤ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_ge {a b : Int} : a ≥ b ↔ Rat.ofInt a ≥ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_gt {a b : Int} : a > b ↔ Rat.ofInt a > Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_eq {a b : Int} : a = b ↔ Rat.ofInt a = Rat.ofInt b := by
  constructor
  · intro h; rw [h]
  · intro h; exact Rat.intCast_inj.mp h

theorem floor_def' (a : Rat) : a.floor = a.num / a.den := by
  rw [Rat.floor]
  split
  · next h => simp [h]
  · next => rfl

theorem intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1 := mk'_eq_divInt

theorem le_floor {z : Int} : ∀ {r : Rat}, z ≤ Rat.floor r ↔ (z : Rat) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp only [Rat.floor_def']
    rw [mk'_eq_divInt]
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    conv =>
      rhs
      rw [Rat.intCast_eq_divInt, Rat.divInt_le_divInt Int.zero_lt_one h', Int.mul_one]
    exact Int.le_ediv_iff_mul_le h'

@[simp]
protected theorem neg_zero : -(0:Rat) = 0 := rfl

protected theorem neg_add (a b : Rat) : -(a + b) = -a + -b := by
  rw [←Rat.sub_eq_add_neg, ←Rat.neg_neg b, ←Rat.sub_eq_add_neg, Rat.neg_sub]
  simp [Rat.sub_eq_add_neg, Rat.add_comm, Rat.neg_neg]

theorem neg_eq_neg_one_mul (a : Rat) : -a = -1 * a :=
  numDenCasesOn a fun n d h h1 => by
    simp [Rat.neg_mkRat, Rat.mul_def, Rat.normalize_eq_mkRat]
    simp [← Rat.divInt_ofNat]
    rw [divInt_num' (Nat.pos_iff_ne_zero.mp h) h1, divInt_den' (Nat.pos_iff_ne_zero.mp h) h1]

protected theorem mul_div_right_comm (a b c : Rat) : a * b / c = a / c * b := by
  rw [div_def, div_def, Rat.mul_assoc, Rat.mul_comm b c⁻¹, Rat.mul_assoc]

protected theorem zero_div (a : Rat) : 0 / a = 0 := by
  simp [div_def]

protected theorem add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  simp [div_def, Rat.add_mul]

def addN : List Rat → Rat
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN, Rat.add_zero, Rat.zero_add]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, Rat.add_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem addN_cons_append : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, Rat.add_zero]

def mulN : List Rat → Rat
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, Rat.mul_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem mulN_cons_append : mulN (x :: xs) = x * mulN xs := by
  cases xs <;> simp only [mulN, Rat.mul_one]

end Rat
