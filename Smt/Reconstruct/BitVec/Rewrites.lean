/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.BitVec.Core

@[expose] public section

namespace Smt.Reconstruct.BitVec.Rewrite

open Function HBitVecList

-- https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites

private theorem sub_eq_zero_iff {w : Nat} {x y : BitVec w} : x - y = 0#w ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· + y) h
    simpa [BitVec.sub_add_cancel] using this
  · rintro rfl
    exact BitVec.sub_self x

private theorem two_mul_natAbs_toInt_le {w : Nat} {x : BitVec w} :
    2 * x.toInt.natAbs ≤ 2 ^ w := by
  have h₁ := BitVec.two_mul_toInt_lt (x := x)
  have h₂ := BitVec.le_two_mul_toInt (x := x)
  have h₃ : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := Int.natCast_pow 2 w
  omega

private theorem toInt_mul_of_two_mul_natAbs_lt {w : Nat} {x y : BitVec w}
    (h : 2 * (x.toInt * y.toInt).natAbs < 2 ^ w) : (x * y).toInt = x.toInt * y.toInt := by
  rw [BitVec.toInt_mul]
  apply Int.bmod_eq_of_le_mul_two <;> omega

-- Core normalization rules

theorem concat_extract_merge {w : Nat} {xs : HBitVecList} {s : BitVec w} {ys : HBitVecList}
    {i j k : Nat} (hij : i ≤ j) (hjk : j < k) :
    (xs ++ s.extractLsb k (j + 1) ::ₕ s.extractLsb j i ::ₕ ys).concat =
    (xs ++ s.extractLsb k i ::ₕ ys).concat.cast (by simp; omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [getLsbD_concat_append, getLsbD_concat_cons, width_cons, BitVec.getLsbD_cast,
    BitVec.getLsbD_extractLsb]
  repeat' split
  all_goals first
    | rfl
    | (congr 1 <;> (try simp only [decide_eq_decide]) <;> (try congr 1) <;> omega)
    | omega

theorem extract_extract {w : Nat} {x : BitVec w} {i j k l : Nat} (hkl : k ≤ l) (hl : l ≤ j - i) :
    (x.extractLsb j i).extractLsb l k = (x.extractLsb (i + l) (i + k)).cast (by omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast]
  have h₁ : k + n < j - i + 1 := by omega
  have h₂ : n < i + l - (i + k) + 1 := by omega
  simp only [hn, h₁, h₂, decide_true, Bool.true_and, Nat.add_assoc]

-- cvc5's `(>= n (- (@bvsize x) 1))` and well-formedness (`n < w`) force `n = w - 1`.
theorem extract_whole {w : Nat} {x : BitVec w} (hw : 0 < w) :
    x.extractLsb (w - 1) 0 = x.cast (by omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast, Nat.zero_add]
  simp only [Nat.sub_zero] at hi
  simp [hi]

-- cvc5's premise `j ≤ w` is replaced by `hj : j < w`, which `(extract j i x)` needs.
theorem extract_concat_1 {w v : Nat} {x : BitVec w} {xs : HBitVecList} {y : BitVec v}
    {i j : Nat} (hij : i ≤ j) (hj : j < w) :
    (xs ++ y ::ₕ x ::ₕ .nil).concat.extractLsb j i = x.extractLsb j i := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, getLsbD_concat_append, getLsbD_concat_cons, width_cons,
    width_nil, concat_nil, Nat.add_zero, Nat.sub_zero]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem extract_concat_2 {w v : Nat} {x : BitVec w} {xs : HBitVecList} {y : BitVec v}
    {i j : Nat} (h₁ : (i < w) = True) (h₂ : (j ≥ w) = True) :
    (xs ++ y ::ₕ x ::ₕ .nil).concat.extractLsb j i =
    ((xs ++ y ::ₕ .nil).concat.extractLsb (j - w) 0 ++ x.extractLsb (w - 1) i).cast
      (by have := of_eq_true h₁; have := of_eq_true h₂; omega) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, getLsbD_concat_append, getLsbD_concat_cons, width_cons,
    width_nil, concat_nil, Nat.add_zero, Nat.sub_zero, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    Nat.zero_add, Nat.not_lt_zero, ite_false]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem extract_concat_3 {w v : Nat} {x : BitVec w} {y : BitVec v} {xs : HBitVecList}
    {i j : Nat} (h : (i ≥ w) = True) :
    (xs ++ y ::ₕ x ::ₕ .nil).concat.extractLsb j i =
    ((xs ++ y ::ₕ .nil).concat.extractLsb (j - w) (i - w)).cast
      (by have := of_eq_true h; omega) := by
  have h := of_eq_true h
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, getLsbD_concat_append, getLsbD_concat_cons, width_cons,
    width_nil, concat_nil, Nat.add_zero, Nat.sub_zero, BitVec.getLsbD_cast]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem extract_concat_4 {w v : Nat} {x : BitVec w} {y : BitVec v} {xs : HBitVecList}
    {i j : Nat} (h : (j < (x ::ₕ y ::ₕ xs).width - w) = True) (hij : i ≤ j) :
    (x ::ₕ (xs ++ y ::ₕ .nil)).concat.extractLsb j i =
    (xs ++ y ::ₕ .nil).concat.extractLsb j i := by
  have h := of_eq_true h
  simp only [width_cons] at h
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, getLsbD_concat_cons, width_append, width_cons, width_nil,
    Nat.add_zero]
  rw [ite_eq_left (by omega)]

-- `y : BitVec (j - i + 1)` keeps the LHS cast-free, so `y` is bound after `i` and `j`.
theorem eq_extract_elim1 {w : Nat} {x : BitVec w} {i j : Nat} {y : BitVec (j - i + 1)}
    (h₁ : (w - 1 > j) = True) (h₂ : (i > 0) = True) (hij : i ≤ j) :
    (x.extractLsb j i = y) =
    (x = (x.extractLsb (w - 1) (j + 1) ++ y ++ x.extractLsb (i - 1) 0).cast
      (by have := of_eq_true h₁; have := of_eq_true h₂; omega)) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  apply propext
  constructor
  · rintro rfl
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)
  · intro hx
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    rw [hx]
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)

theorem eq_extract_elim2 {w : Nat} {x : BitVec w} {j : Nat} {y : BitVec (j - 0 + 1)}
    (h : (w - 1 > j) = True) :
    (x.extractLsb j 0 = y) =
    (x = (x.extractLsb (w - 1) (j + 1) ++ y).cast (by have := of_eq_true h; omega)) := by
  have h := of_eq_true h
  apply propext
  constructor
  · rintro rfl
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)
  · intro hx
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    rw [hx]
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)

theorem eq_extract_elim3 {w : Nat} {x : BitVec w} {i : Nat} {y : BitVec (w - 1 - i + 1)}
    (h : (i > 0) = True) (hi : i < w) :
    (x.extractLsb (w - 1) i = y) =
    (x = (y ++ x.extractLsb (i - 1) 0).cast (by have := of_eq_true h; omega)) := by
  have h := of_eq_true h
  apply propext
  constructor
  · rintro rfl
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)
  · intro hx
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    rw [hx]
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb]
    repeat' split
    all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
    all_goals first | rfl | omega | (congr 1; omega)

-- Normalization rules

theorem extract_not {w : Nat} {x : BitVec w} {i j : Nat} (hij : i ≤ j) (hj : j < w) :
    (~~~x).extractLsb j i = ~~~(x.extractLsb j i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp (disch := omega) only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_not, decide_eq_true,
    Bool.true_and]

theorem extract_sign_extend_1 {w : Nat} {x : BitVec w} {low high k : Nat}
    (h : (high < w) = True) (hlh : low ≤ high) :
    (x.signExtend (w + k)).extractLsb high low = x.extractLsb high low := by
  have h := of_eq_true h
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp (disch := omega) only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, decide_eq_true,
    Bool.true_and, ite_eq_left]

theorem extract_sign_extend_2 {w : Nat} {x : BitVec w} {low high k : Nat}
    (h₁ : (low < w) = True) (h₂ : (high ≥ w) = True) (hhigh : high < w + k) :
    (x.signExtend (w + k)).extractLsb high low =
    ((x.extractLsb (w - 1) low).signExtend (w - 1 - low + 1 + (1 + (high - w)))).cast
      (by have := of_eq_true h₁; have := of_eq_true h₂; omega) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, BitVec.getLsbD_cast,
    BitVec.msb_eq_getLsbD_last]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem extract_sign_extend_3 {w : Nat} {x : BitVec w} {low high k : Nat}
    (h : (low ≥ w) = True) (hlh : low ≤ high) (hhigh : high < w + k) :
    (x.signExtend (w + k)).extractLsb high low =
    ((x.extractLsb (w - 1) (w - 1)).replicate (1 + (high - low))).cast
      (by rw [Nat.sub_self, Nat.zero_add, Nat.one_mul]; omega) := by
  have h := of_eq_true h
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, BitVec.getLsbD_cast,
    BitVec.getLsbD_replicate, BitVec.msb_eq_getLsbD_last, Nat.sub_self, Nat.zero_add, Nat.mod_one,
    Nat.add_zero]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem not_xor {w : Nat} {x1 x2 : BitVec w} {xs : List (BitVec w)} :
    ~~~(BitVec.xorN (x1 :: x2 :: xs)) = BitVec.xorN (~~~x1 :: x2 :: xs) := by
  simp only [BitVec.xorN_cons, BitVec.not_xor_left]

theorem and_simplify_1 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.andN (xs ++ ~~~x :: (ys ++ x :: zs)) = 0#w := by
  ext i hi
  simp only [BitVec.andN_append, BitVec.andN_cons, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_zero]
  cases x[i] <;> simp

theorem and_simplify_2 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.andN (xs ++ x :: (ys ++ ~~~x :: zs)) = 0#w := by
  ext i hi
  simp only [BitVec.andN_append, BitVec.andN_cons, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_zero]
  cases x[i] <;> simp

theorem or_simplify_1 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.orN (xs ++ ~~~x :: (ys ++ x :: zs)) = ~~~(0#w) := by
  ext i hi
  simp only [BitVec.orN_append, BitVec.orN_cons, BitVec.getElem_or, BitVec.getElem_not,
    BitVec.getElem_zero]
  cases x[i] <;> simp

theorem or_simplify_2 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.orN (xs ++ x :: (ys ++ ~~~x :: zs)) = ~~~(0#w) := by
  ext i hi
  simp only [BitVec.orN_append, BitVec.orN_cons, BitVec.getElem_or, BitVec.getElem_not,
    BitVec.getElem_zero]
  cases x[i] <;> simp

theorem xor_simplify_1 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.xorN (xs ++ x :: (ys ++ x :: zs)) = BitVec.xorN (xs ++ (ys ++ zs)) := by
  ext i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getElem_xor]
  cases x[i] <;> simp

theorem xor_simplify_2 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.xorN (xs ++ x :: (ys ++ ~~~x :: zs)) = ~~~(BitVec.xorN (xs ++ (ys ++ zs))) := by
  ext i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getElem_xor, BitVec.getElem_not]
  cases x[i] <;> simp

theorem xor_simplify_3 {w : Nat} {xs ys zs : List (BitVec w)} {x : BitVec w} :
    BitVec.xorN (xs ++ ~~~x :: (ys ++ x :: zs)) = ~~~(BitVec.xorN (xs ++ (ys ++ zs))) := by
  ext i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getElem_xor, BitVec.getElem_not]
  cases x[i] <;> simp

-- Simplify bit-blasting

theorem ult_add_one {w : Nat} {x : BitVec w} {ys zs : List (BitVec w)} :
    (x < BitVec.addN (ys ++ 1#w :: zs)) =
    (¬(BitVec.addN (ys ++ zs) = ~~~(0#w)) ∧ ¬(BitVec.addN (ys ++ zs) < x)) := by
  simp only [BitVec.addN_append, BitVec.addN_cons]
  generalize BitVec.addN ys = a
  generalize BitVec.addN zs = b
  rw [BitVec.add_comm 1#w b, ← BitVec.add_assoc]
  generalize a + b = s
  apply propext
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · bv_omega
  · have h1 : (1#w).toNat = 1 := by simp [Nat.one_mod_two_pow hw]
    have hs := s.isLt
    rw [BitVec.lt_def, BitVec.toNat_add, h1, BitVec.toNat_eq, BitVec.toNat_not, BitVec.toNat_ofNat,
      Nat.zero_mod, BitVec.lt_def]
    by_cases hs1 : s.toNat + 1 = 2 ^ w
    · rw [hs1, Nat.mod_self]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

-- `(sign_extend m a)` is written with the common target width: `a.signExtend (tn + n)`.
theorem mult_slt_mult_1 {tn an : Nat} {x y : BitVec tn} {a : BitVec an} {n m : Nat}
    (h₁ : (n ≥ tn) = True) (h₂ : (m ≥ an) = True) (hw : tn + n = an + m) :
    ((y.signExtend (tn + n) * a.signExtend (tn + n)).slt
      (x.signExtend (tn + n) * a.signExtend (tn + n)) = true) =
    (¬(y - x = 0#tn) ∧ ¬(a = 0#an) ∧ ((y.slt x = true) = ((0#an).slt a = true))) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  have hW : 2 ^ tn * 2 ^ an ≤ 2 ^ (tn + n) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hmul : ∀ z : BitVec tn,
      (z.signExtend (tn + n) * a.signExtend (tn + n)).toInt = z.toInt * a.toInt := by
    intro z
    have hz : (z.signExtend (tn + n)).toInt = z.toInt := BitVec.toInt_signExtend_of_le (by omega)
    have ha : (a.signExtend (tn + n)).toInt = a.toInt := BitVec.toInt_signExtend_of_le (by omega)
    rw [toInt_mul_of_two_mul_natAbs_lt, hz, ha]
    rw [hz, ha, Int.natAbs_mul]
    have := Nat.mul_le_mul (two_mul_natAbs_toInt_le (x := z)) (two_mul_natAbs_toInt_le (x := a))
    rw [Nat.mul_mul_mul_comm] at this
    have := Nat.two_pow_pos (tn + n)
    omega
  apply propext
  rw [BitVec.slt_iff_toInt_lt, hmul, hmul, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt,
    BitVec.toInt_zero, sub_eq_zero_iff, ← BitVec.toInt_inj, ← BitVec.toInt_inj (y := 0#an),
    BitVec.toInt_zero, eq_iff_iff]
  rcases Int.lt_trichotomy a.toInt 0 with hA | hA | hA
  · rw [Int.mul_lt_mul_right_of_neg hA]
    omega
  · simp [hA]
  · rw [Int.mul_lt_mul_right hA]
    omega

theorem mult_slt_mult_2 {tn an : Nat} {x y : BitVec tn} {a : BitVec an} {n m : Nat}
    (h₁ : (n ≥ tn) = True) (h₂ : (m ≥ an) = True) (hw : tn + n = an + m) :
    ((y.zeroExtend (tn + n) * a.signExtend (tn + n)).slt
      (x.zeroExtend (tn + n) * a.signExtend (tn + n)) = true) =
    (¬(y - x = 0#tn) ∧ ¬(a = 0#an) ∧ ((y < x) = ((0#an).slt a = true))) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  have hW : 2 ^ tn * 2 ^ an ≤ 2 ^ (tn + n) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos an
  have hmul : ∀ z : BitVec tn,
      (z.zeroExtend (tn + n) * a.signExtend (tn + n)).toInt = z.toNat * a.toInt := by
    intro z
    have hz : (z.zeroExtend (tn + n)).toInt = z.toNat := by
      rw [BitVec.toInt_setWidth]
      apply Int.bmod_eq_of_le_mul_two
      · omega
      · have := z.isLt
        have : 2 ^ tn * 2 ≤ 2 ^ (tn + n) ∨ tn = 0 := by
          rcases Nat.eq_zero_or_pos tn with h | h
          · exact Or.inr h
          · rw [← Nat.pow_succ]
            exact Or.inl (Nat.pow_le_pow_right (by decide) (by omega))
        rcases this with h | h
        · omega
        · subst h; have := Nat.two_pow_pos n; omega
    have ha : (a.signExtend (tn + n)).toInt = a.toInt := BitVec.toInt_signExtend_of_le (by omega)
    rw [toInt_mul_of_two_mul_natAbs_lt, hz, ha]
    rw [hz, ha, Int.natAbs_mul, Int.natAbs_natCast]
    have := Nat.mul_le_mul (Nat.le_sub_one_of_lt z.isLt) (two_mul_natAbs_toInt_le (x := a))
    rw [Nat.sub_one_mul, Nat.mul_left_comm] at this
    have := Nat.two_pow_pos (tn + n)
    omega
  apply propext
  rw [BitVec.slt_iff_toInt_lt, hmul, hmul, BitVec.lt_def, BitVec.slt_iff_toInt_lt,
    BitVec.toInt_zero, sub_eq_zero_iff, ← BitVec.toNat_inj, ← BitVec.toInt_inj (y := 0#an),
    BitVec.toInt_zero, eq_iff_iff]
  rcases Int.lt_trichotomy a.toInt 0 with hA | hA | hA
  · rw [Int.mul_lt_mul_right_of_neg hA]
    omega
  · simp [hA]
  · rw [Int.mul_lt_mul_right hA]
    omega

-- Commutativity

theorem commutative_xor {w : Nat} {x y : BitVec w} : x ^^^ y = y ^^^ x :=
  BitVec.xor_comm x y

theorem commutative_comp {w : Nat} {x y : BitVec w} : x.smtComp y = y.smtComp x := by
  simp only [BitVec.smtComp, eq_comm]

theorem zero_extend_eliminate_0 {w : Nat} {x : BitVec w} : x.zeroExtend (w + 0) = x :=
  BitVec.setWidth_eq x

theorem sign_extend_eliminate_0 {w : Nat} {x : BitVec w} : x.signExtend (w + 0) = x :=
  BitVec.signExtend_eq x

theorem not_neq {w : Nat} {x : BitVec w} (h : (w > 0) = True) : (x = ~~~x) = False := by
  apply eq_false
  intro hx
  have := congrArg (·.getLsbD 0) hx
  simp [of_eq_true h] at this

theorem ult_ones {w : Nat} {x : BitVec w} :
    (x < BitVec.ofNat w (2 ^ w - 1)) = (x ≠ BitVec.ofNat w (2 ^ w - 1)) := by
  rw [BitVec.ofNat_two_pow_sub_one]
  exact propext BitVec.lt_allOnes_iff

-- Collapse rules

theorem concat_merge_const {xs : HBitVecList} {n1 w1 n2 w2 : Nat} {zs : HBitVecList} :
    (xs ++ BitVec.ofNat w1 n1 ::ₕ BitVec.ofNat w2 n2 ::ₕ zs).concat =
    (xs ++ BitVec.ofNat (w1 + w2) (n1 * 2 ^ w2 + n2 % 2 ^ w2) ::ₕ zs).concat.cast
      (by simp only [width_append, width_cons]; omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_cast, getLsbD_concat_append, getLsbD_concat_cons, width_cons,
    BitVec.getLsbD_ofNat, Nat.mul_comm n1,
    Nat.testBit_two_pow_mul_add n1 (Nat.mod_lt n2 (Nat.two_pow_pos w2)), Nat.testBit_mod_two_pow]
  repeat' split
  all_goals (try simp (disch := omega) only [decide_eq_true, Bool.true_and])
  all_goals first | rfl | omega | (congr 1; omega)

theorem commutative_add {w : Nat} {x y : BitVec w} : x + y = y + x :=
  BitVec.add_comm x y

theorem sub_eliminate {w : Nat} {x y : BitVec w} : x - y = x + -y :=
  BitVec.sub_eq_add_neg x y

theorem ite_width_one {x : BitVec 1} : (if x = 1#1 then 1#1 else 0#1) = x := by
  revert x; decide

theorem ite_width_one_not {x : BitVec 1} : (if x = 0#1 then 1#1 else 0#1) = ~~~x := by
  revert x; decide

theorem eq_xor_solve {w : Nat} {x y z : BitVec w} : ((x ^^^ y = z) = (x = z ^^^ y)) = True := by
  apply eq_true
  apply propext
  constructor
  · rintro rfl
    simp [BitVec.xor_assoc]
  · rintro rfl
    simp [BitVec.xor_assoc]

theorem eq_not_solve {w : Nat} {x y : BitVec w} : ((~~~x = y) = (x = ~~~y)) = True := by
  apply eq_true
  apply propext
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

end Smt.Reconstruct.BitVec.Rewrite
