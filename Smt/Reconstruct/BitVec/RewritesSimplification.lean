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

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites-simplification

private theorem bv1_cases (c : BitVec 1) : c = 0#1 ∨ c = 1#1 := by
  bv_omega

private theorem toNat_ofNat_of_lt {w n : Nat} (h : n < w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h Nat.lt_two_pow_self)]

private theorem shiftLeft_nat_eq {w k : Nat} {x : BitVec w} (h : k < w) :
    x <<< k = x <<< BitVec.ofNat w k := by
  rw [BitVec.shiftLeft_eq', toNat_ofNat_of_lt h]

private theorem ushiftRight_nat_eq {w k : Nat} {x : BitVec w} (h : k < w) :
    x >>> k = x >>> BitVec.ofNat w k := by
  rw [BitVec.ushiftRight_eq', toNat_ofNat_of_lt h]

private theorem shiftLeft_ofNat_eq {w amount en : Nat} {x : BitVec w} (h : amount < w)
    (hen : en = w - (1 + amount)) :
    x <<< BitVec.ofNat w amount = (x.extractLsb en 0 ++ 0#amount).cast (by omega) := by
  subst hen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.shiftLeft_eq', toNat_ofNat_of_lt h]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb, BitVec.getLsbD_zero]
  split <;> simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and,
    Bool.and_true, Bool.false_and, Bool.and_false, Bool.not_true, Bool.not_false, Nat.zero_add]

private theorem ofNat_two_pow {w k : Nat} : BitVec.ofNat w (2 ^ k) = BitVec.twoPow w k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]

-- `Nat.isPowerOfTwo` is not exposed, so its witness is recovered through its bitwise characterization:
-- otherwise bit `n.log2` would be set in both `n` and `n - 1`.
private theorem eq_two_pow_log2 {n : Nat} (h : n.isPowerOfTwo = True) : n = 2 ^ n.log2 := by
  obtain ⟨hn, hand⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mpr (of_eq_true h)
  have hle : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn
  have hlt : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have bit : ∀ m, 2 ^ n.log2 ≤ m → m < 2 ^ (n.log2 + 1) → m.testBit n.log2 = true := by
    intro m h₁ h₂
    obtain ⟨r, rfl⟩ : ∃ r, m = 2 ^ n.log2 + r := ⟨m - 2 ^ n.log2, by omega⟩
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [Nat.pow_succ] at h₂; omega)]
    rfl
  refine Nat.le_antisymm (Nat.le_of_not_lt fun hgt => ?_) hle
  have := congrArg (·.testBit n.log2) hand
  simp only [Nat.testBit_and, bit n hle hlt, bit (n - 1) (by omega) (by omega),
    Nat.zero_testBit] at this
  contradiction

private theorem ofNat_eq_twoPow_log2 {w n : Nat} (h : n.isPowerOfTwo = True) :
    BitVec.ofNat w n = BitVec.twoPow w n.log2 :=
  (congrArg (BitVec.ofNat w) (eq_two_pow_log2 h)).trans ofNat_two_pow

private theorem ofNat_two_pow_sub {w k n : Nat} (hk : 2 ^ w - n = 2 ^ k) (hn : 0 < n) :
    BitVec.ofNat w n = -BitVec.twoPow w k := by
  apply BitVec.eq_of_toNat_eq
  have h0 := Nat.two_pow_pos k
  have h1 := Nat.two_pow_pos w
  rw [BitVec.toNat_ofNat, BitVec.toNat_neg, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (a := 2 ^ k) (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem mulN_cons_cons_comm {w : Nat} {xs ys : List (BitVec w)} {z c : BitVec w} :
    BitVec.mulN (xs ++ z :: c :: ys) = BitVec.mulN (xs ++ z :: ys) * c := by
  simp only [BitVec.mulN_append, BitVec.mulN_cons, BitVec.mul_assoc]
  congr 2
  rw [BitVec.mul_comm c]

/-- A bit-vector with a constant prefix `a` of width `n` is below `2 ^ (n + w - lz)`, where `lz`
is the number of leading zeros of the prefix (`lz = 0` if `a ≥ 2 ^ n`). -/
private theorem toNat_ofNat_append_lt {n w a : Nat} {x : BitVec w} :
    (BitVec.ofNat n a ++ x).toNat < 2 ^ (n + w - (if a = 0 then n else n - (1 + a.log2))) := by
  by_cases ha : a < 2 ^ n
  · rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    split
    · subst a
      rw [Nat.zero_shiftLeft, Nat.zero_or, show n + w - n = w by omega]
      exact x.isLt
    · rename_i ha0
      have hlog : a.log2 < n := (Nat.log2_lt ha0).mpr ha
      rw [show n + w - (n - (1 + a.log2)) = (a.log2 + 1) + w by omega]
      apply Nat.or_lt_two_pow
      · rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos w)
      · exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ Nat.two_pow_pos n)
    have hlog : n ≤ a.log2 := Nat.not_lt.mp (mt (Nat.log2_lt ha0).mp ha)
    rw [ite_eq_right ha0, show n - (1 + a.log2) = 0 by omega, Nat.sub_zero]
    exact (BitVec.ofNat n a ++ x).isLt

private theorem toNat_eq_of_eq_zeroExtend {w nm : Nat} {C : BitVec nm} (hw : 0 < w)
    (h : C = (C.extractLsb (w - 1) 0).zeroExtend nm) (hnm : w ≤ nm) :
    C.toNat = (C.extractLsb (w - 1) 0).toNat := by
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at h'
  rw [h', Nat.mod_eq_of_lt]
  calc (C.extractLsb (w - 1) 0).toNat < 2 ^ (w - 1 - 0 + 1) := BitVec.isLt _
    _ ≤ 2 ^ nm := Nat.pow_le_pow_right (by decide) (by omega)

private theorem toNat_signExtend_of_le {w v : Nat} {x : BitVec w} (h : w ≤ v) :
    (x.signExtend v).toNat = x.toNat + if x.msb then 2 ^ v - 2 ^ w else 0 := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt
    (Nat.pow_le_pow_right (by decide) h))]

private theorem toNat_one_shiftLeft {v k : Nat} (h : k < v) :
    (1#v <<< BitVec.ofNat v k).toNat = 2 ^ k := by
  rw [BitVec.shiftLeft_eq', toNat_ofNat_of_lt h, ← BitVec.twoPow_eq, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)]

private theorem toNat_allOnes_shiftLeft {v k : Nat} (h : k < v) :
    (~~~(0#v) <<< BitVec.ofNat v k).toNat = 2 ^ v - 2 ^ k := by
  rw [BitVec.shiftLeft_eq', toNat_ofNat_of_lt h, BitVec.toNat_shiftLeft, BitVec.toNat_not,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, Nat.shiftLeft_eq]
  have hB := Nat.two_pow_pos k
  have hBA : 2 ^ k < 2 ^ v := Nat.pow_lt_pow_right (by decide) h
  have hP : 2 ^ v ≤ 2 ^ v * 2 ^ k := Nat.le_mul_of_pos_right _ hB
  rw [Nat.sub_one_mul, show 2 ^ v * 2 ^ k - 2 ^ k = 2 ^ v * (2 ^ k - 1) + (2 ^ v - 2 ^ k) by
    rw [Nat.mul_sub_one]; omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private theorem mod_two_pow_of_ge {n v w : Nat} (hwv : w ≤ v) (h₁ : 2 ^ v - 2 ^ w ≤ n)
    (h₂ : n < 2 ^ v) : n % 2 ^ w = n - (2 ^ v - 2 ^ w) := by
  have hv : 2 ^ v = 2 ^ w * 2 ^ (v - w) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hwv]
  have hW : 2 ^ w ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hwv
  have hn : n = 2 ^ w * (2 ^ (v - w) - 1) + (n - (2 ^ v - 2 ^ w)) := by
    rw [Nat.mul_sub_one, ← hv]; omega
  calc n % 2 ^ w = (2 ^ w * (2 ^ (v - w) - 1) + (n - (2 ^ v - 2 ^ w))) % 2 ^ w :=
        congrArg (· % 2 ^ w) hn
    _ = (n - (2 ^ v - 2 ^ w)) % 2 ^ w := Nat.mul_add_mod ..
    _ = n - (2 ^ v - 2 ^ w) := Nat.mod_eq_of_lt (by omega)

private theorem toNat_extractLsb_low {v w : Nat} {C : BitVec v} (hw : 0 < w) :
    (C.extractLsb (w - 1) 0).toNat = C.toNat % 2 ^ w := by
  rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero, show w - 1 - 0 + 1 = w by omega]

-- Simplification Rules

theorem ite_equal_children {w : Nat} {c : BitVec 1} {x : BitVec w} :
    BitVec.smtIte c x x = x := by
  simp only [BitVec.smtIte, ite_self]
theorem ite_const_children_1 {c : BitVec 1} :
    BitVec.smtIte c (0#1) (1#1) = ~~~c := by
  rcases bv1_cases c with rfl | rfl <;> decide
theorem ite_const_children_2 {c : BitVec 1} :
    BitVec.smtIte c (1#1) (0#1) = c := by
  rcases bv1_cases c with rfl | rfl <;> decide
theorem ite_equal_cond_1 {w : Nat} {c0 : BitVec 1} {t0 e0 e1 : BitVec w} :
    BitVec.smtIte c0 (BitVec.smtIte c0 t0 e0) e1 = BitVec.smtIte c0 t0 e1 := by
  simp only [BitVec.smtIte]; split <;> simp_all
theorem ite_equal_cond_2 {w : Nat} {c0 : BitVec 1} {t0 t1 e1 : BitVec w} :
    BitVec.smtIte c0 t0 (BitVec.smtIte c0 t1 e1) = BitVec.smtIte c0 t0 e1 := by
  simp only [BitVec.smtIte]; split <;> simp_all
theorem ite_equal_cond_3 {w : Nat} {c0 : BitVec 1} {t0 e0 t1 e1 : BitVec w} :
    BitVec.smtIte c0 (BitVec.smtIte c0 t0 e0) (BitVec.smtIte c0 t1 e1) =
      BitVec.smtIte c0 t0 e1 := by
  simp only [BitVec.smtIte]; split <;> simp_all
theorem ite_merge_then_if {w : Nat} {c0 c1 : BitVec 1} {t1 e1 : BitVec w} :
    BitVec.smtIte c0 (BitVec.smtIte c1 t1 e1) t1 = BitVec.smtIte (c0 &&& ~~~c1) e1 t1 := by
  rcases bv1_cases c0 with rfl | rfl <;> rcases bv1_cases c1 with rfl | rfl <;>
    simp [BitVec.smtIte]
theorem ite_merge_else_if {w : Nat} {c0 c1 : BitVec 1} {t1 e1 : BitVec w} :
    BitVec.smtIte c0 (BitVec.smtIte c1 t1 e1) e1 = BitVec.smtIte (c0 &&& c1) t1 e1 := by
  rcases bv1_cases c0 with rfl | rfl <;> rcases bv1_cases c1 with rfl | rfl <;>
    simp [BitVec.smtIte]
theorem ite_merge_then_else {w : Nat} {c0 c1 : BitVec 1} {t0 e1 : BitVec w} :
    BitVec.smtIte c0 t0 (BitVec.smtIte c1 t0 e1) = BitVec.smtIte (~~~c0 &&& ~~~c1) e1 t0 := by
  rcases bv1_cases c0 with rfl | rfl <;> rcases bv1_cases c1 with rfl | rfl <;>
    simp [BitVec.smtIte]
theorem ite_merge_else_else {w : Nat} {c0 c1 : BitVec 1} {t1 t0 : BitVec w} :
    BitVec.smtIte c0 t0 (BitVec.smtIte c1 t1 t0) = BitVec.smtIte (~~~c0 &&& c1) t1 t0 := by
  rcases bv1_cases c0 with rfl | rfl <;> rcases bv1_cases c1 with rfl | rfl <;>
    simp [BitVec.smtIte]

theorem shl_by_const_0 {w : Nat} {x : BitVec w} : x <<< 0#w = x := by
  simp [BitVec.shiftLeft_eq']
theorem shl_by_const_1 {w : Nat} {x : BitVec w} {amount : Nat} (h : (amount < w) = True) :
    x <<< BitVec.ofNat w amount =
      (x.extractLsb (w - (1 + amount)) 0 ++ 0#amount).cast (by have := of_eq_true h; omega) :=
  shiftLeft_ofNat_eq (of_eq_true h) rfl
theorem shl_by_const_2 {w : Nat} {x : BitVec w} {amount : Nat}
    (h₁ : (amount ≥ w) = True) (h₂ : (amount < 2 ^ w) = True) :
    x <<< BitVec.ofNat w amount = 0#w := by
  rw [BitVec.shiftLeft_ofNat_eq, Nat.mod_eq_of_lt (of_eq_true h₂)]
  exact BitVec.shiftLeft_eq_zero (of_eq_true h₁)
theorem lshr_by_const_0 {w : Nat} {x : BitVec w} : x >>> 0#w = x := by
  simp [BitVec.ushiftRight_eq']
theorem lshr_by_const_1 {w : Nat} {x : BitVec w} {amount : Nat} (h : (amount < w) = True) :
    x >>> BitVec.ofNat w amount =
      (0#amount ++ x.extractLsb (w - 1) amount).cast (by have := of_eq_true h; omega) := by
  have h := of_eq_true h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.ushiftRight_eq', toNat_ofNat_of_lt h]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb, BitVec.getLsbD_zero]
  split
  · simp (disch := omega) only [decide_eq_true, Bool.true_and]
  · exact BitVec.getLsbD_of_ge x _ (by omega)
theorem lshr_by_const_2 {w : Nat} {x : BitVec w} {amount : Nat}
    (h₁ : (amount ≥ w) = True) (h₂ : (amount < 2 ^ w) = True) :
    x >>> BitVec.ofNat w amount = 0#w := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (of_eq_true h₂)]
  exact BitVec.ushiftRight_eq_zero (of_eq_true h₁)
theorem ashr_by_const_0 {w : Nat} {x : BitVec w} : x.sshiftRight' 0#w = x := by
  simp [BitVec.sshiftRight']
theorem ashr_by_const_1 {w : Nat} {x : BitVec w} {amount : Nat} (h : (amount < w) = True) :
    x.sshiftRight' (BitVec.ofNat w amount) =
      ((x.extractLsb (w - 1) (w - 1)).replicate amount ++ x.extractLsb (w - 1) amount).cast
        (by have := of_eq_true h; rw [Nat.sub_self, Nat.zero_add, Nat.one_mul]; omega) := by
  have h := of_eq_true h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight', toNat_ofNat_of_lt h, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, BitVec.getLsbD_replicate,
    BitVec.msb_eq_getLsbD_last, Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.mod_one,
    Nat.add_zero]
  split <;> split <;> simp (disch := omega) only [decide_eq_true, decide_eq_false,
    Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and, Nat.add_comm]
  all_goals omega
theorem ashr_by_const_2 {w : Nat} {x : BitVec w} {amount : Nat}
    (h₁ : (amount ≥ w) = True) (h₂ : (amount < 2 ^ w) = True) :
    x.sshiftRight' (BitVec.ofNat w amount) =
      ((x.extractLsb (w - 1) (w - 1)).replicate w).cast
        (by rw [Nat.sub_self, Nat.zero_add, Nat.one_mul]) := by
  have h₁ := of_eq_true h₁
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hamt : (BitVec.ofNat w amount).toNat = amount := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (of_eq_true h₂)]
  simp only [BitVec.getLsbD_sshiftRight', hamt, BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_replicate, BitVec.msb_eq_getLsbD_last, Nat.sub_self, Nat.zero_add,
    Nat.one_mul, Nat.mod_one, Nat.add_zero]
  split <;> simp (disch := omega) only [decide_eq_true, decide_eq_false,
    Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and]
  omega

-- AndOrXorConcatPullUp

-- In `*_concat_pullup` and `*_concat_pullup2`, `y z ys` are bound before `xs ws` because the
-- element width of `xs ws` is the width of the concat.
theorem and_concat_pullup {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (ys ++ z ::ₕ y ::ₕ .nil).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.andN (xs ++ (ys ++ z ::ₕ y ::ₕ .nil).concat :: ws) =
      ((((BitVec.andN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1) wy).cast
            (by simp; omega) &&& (ys ++ z ::ₕ .nil).concat) ++
        (((BitVec.andN (xs ++ ws)).extractLsb (wy - 1) 0).cast (by omega) &&& y)).cast
        (by simp; omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.andN_append, BitVec.andN_cons, BitVec.getLsbD_and, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_append,
    HBitVecList.getLsbD_concat_cons, HBitVecList.width_cons, HBitVecList.width_nil,
    HBitVecList.width_append, Nat.not_lt_zero, ite_false, Nat.sub_zero, Nat.add_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem or_concat_pullup {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (ys ++ z ::ₕ y ::ₕ .nil).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.orN (xs ++ (ys ++ z ::ₕ y ::ₕ .nil).concat :: ws) =
      ((((BitVec.orN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1) wy).cast
            (by simp; omega) ||| (ys ++ z ::ₕ .nil).concat) ++
        (((BitVec.orN (xs ++ ws)).extractLsb (wy - 1) 0).cast (by omega) ||| y)).cast
        (by simp; omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.orN_append, BitVec.orN_cons, BitVec.getLsbD_or, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_append,
    HBitVecList.getLsbD_concat_cons, HBitVecList.width_cons, HBitVecList.width_nil,
    HBitVecList.width_append, Nat.not_lt_zero, ite_false, Nat.sub_zero, Nat.add_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem xor_concat_pullup {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (ys ++ z ::ₕ y ::ₕ .nil).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.xorN (xs ++ (ys ++ z ::ₕ y ::ₕ .nil).concat :: ws) =
      ((((BitVec.xorN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1) wy).cast
            (by simp; omega) ^^^ (ys ++ z ::ₕ .nil).concat) ++
        (((BitVec.xorN (xs ++ ws)).extractLsb (wy - 1) 0).cast (by omega) ^^^ y)).cast
        (by simp; omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getLsbD_xor, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_append,
    HBitVecList.getLsbD_concat_cons, HBitVecList.width_cons, HBitVecList.width_nil,
    HBitVecList.width_append, Nat.not_lt_zero, ite_false, Nat.sub_zero, Nat.add_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]
       simp only [Bool.xor_comm, Bool.xor_left_comm, Bool.xor_assoc])

theorem and_concat_pullup2 {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (z ::ₕ y ::ₕ ys).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.andN (xs ++ (z ::ₕ y ::ₕ ys).concat :: ws) =
      ((((BitVec.andN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1)
            ((z ::ₕ y ::ₕ ys).width - wz)).cast (by simp; omega) &&& z) ++
        (((BitVec.andN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - wz - 1) 0).cast
            (by simp; omega) &&& (y ::ₕ ys).concat)).cast
        (by simp) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.andN_append, BitVec.andN_cons, BitVec.getLsbD_and, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_cons,
    HBitVecList.width_cons, Nat.sub_zero, Nat.add_sub_cancel_left] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem or_concat_pullup2 {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (z ::ₕ y ::ₕ ys).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.orN (xs ++ (z ::ₕ y ::ₕ ys).concat :: ws) =
      ((((BitVec.orN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1)
            ((z ::ₕ y ::ₕ ys).width - wz)).cast (by simp; omega) ||| z) ++
        (((BitVec.orN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - wz - 1) 0).cast
            (by simp; omega) ||| (y ::ₕ ys).concat)).cast
        (by simp) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.orN_append, BitVec.orN_cons, BitVec.getLsbD_or, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_cons,
    HBitVecList.width_cons, Nat.sub_zero, Nat.add_sub_cancel_left] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem xor_concat_pullup2 {wy wz : Nat} {y : BitVec wy} {z : BitVec wz} {ys : HBitVecList}
    {xs ws : List (BitVec (z ::ₕ y ::ₕ ys).width)} (hy : 0 < wy) (hz : 0 < wz) :
    BitVec.xorN (xs ++ (z ::ₕ y ::ₕ ys).concat :: ws) =
      ((((BitVec.xorN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - 1)
            ((z ::ₕ y ::ₕ ys).width - wz)).cast (by simp; omega) ^^^ z) ++
        (((BitVec.xorN (xs ++ ws)).extractLsb ((z ::ₕ y ::ₕ ys).width - wz - 1) 0).cast
            (by simp; omega) ^^^ (y ::ₕ ys).concat)).cast
        (by simp) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getLsbD_xor, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, HBitVecList.getLsbD_concat_cons,
    HBitVecList.width_cons, Nat.sub_zero, Nat.add_sub_cancel_left] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]
       simp only [Bool.xor_comm, Bool.xor_left_comm, Bool.xor_assoc])

theorem and_concat_pullup3 {wy wz wu : Nat} {xs ws : List (BitVec (wz + wy + wu))}
    {y : BitVec wy} {z : BitVec wz} {u : BitVec wu} (hy : 0 < wy) (hz : 0 < wz) (hu : 0 < wu) :
    BitVec.andN (xs ++ (z ++ y ++ u) :: ws) =
      (((BitVec.andN (xs ++ ws)).extractLsb (wu + wy + wz - 1) (wy + wu)).cast (by omega) &&& z) ++
        (((BitVec.andN (xs ++ ws)).extractLsb (wy + wu - 1) wu).cast (by omega) &&& y) ++
        (((BitVec.andN (xs ++ ws)).extractLsb (wu - 1) 0).cast (by omega) &&& u) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.andN_append, BitVec.andN_cons, BitVec.getLsbD_and, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, Nat.sub_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem or_concat_pullup3 {wy wz wu : Nat} {xs ws : List (BitVec (wz + wy + wu))}
    {y : BitVec wy} {z : BitVec wz} {u : BitVec wu} (hy : 0 < wy) (hz : 0 < wz) (hu : 0 < wu) :
    BitVec.orN (xs ++ (z ++ y ++ u) :: ws) =
      (((BitVec.orN (xs ++ ws)).extractLsb (wu + wy + wz - 1) (wy + wu)).cast (by omega) ||| z) ++
        (((BitVec.orN (xs ++ ws)).extractLsb (wy + wu - 1) wu).cast (by omega) ||| y) ++
        (((BitVec.orN (xs ++ ws)).extractLsb (wu - 1) 0).cast (by omega) ||| u) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.orN_append, BitVec.orN_cons, BitVec.getLsbD_or, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, Nat.sub_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]; ac_rfl)
theorem xor_concat_pullup3 {wy wz wu : Nat} {xs ws : List (BitVec (wz + wy + wu))}
    {y : BitVec wy} {z : BitVec wz} {u : BitVec wu} (hy : 0 < wy) (hz : 0 < wz) (hu : 0 < wu) :
    BitVec.xorN (xs ++ (z ++ y ++ u) :: ws) =
      (((BitVec.xorN (xs ++ ws)).extractLsb (wu + wy + wz - 1) (wy + wu)).cast (by omega) ^^^ z) ++
        (((BitVec.xorN (xs ++ ws)).extractLsb (wy + wu - 1) wu).cast (by omega) ^^^ y) ++
        (((BitVec.xorN (xs ++ ws)).extractLsb (wu - 1) 0).cast (by omega) ^^^ u) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.getLsbD_xor, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, Nat.sub_zero] at hi ⊢
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and, Nat.add_zero,
        Nat.add_sub_cancel', Nat.sub_sub, Nat.add_comm]
       simp only [Bool.xor_comm, Bool.xor_left_comm, Bool.xor_assoc])

theorem xor_duplicate {w : Nat} {x : BitVec w} : x ^^^ x = 0#w :=
  BitVec.xor_self

theorem xor_ones {w : Nat} {xs zs : List (BitVec w)} :
    BitVec.xorN (xs ++ BitVec.ofNat w (2 ^ w - 1) :: zs) = ~~~(BitVec.xorN (xs ++ zs)) := by
  simp only [BitVec.xorN_append, BitVec.xorN_cons, BitVec.ofNat_two_pow_sub_one]
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_not, BitVec.getElem_allOnes]
  cases (BitVec.xorN xs)[i] <;> cases (BitVec.xorN zs)[i] <;> rfl

theorem xor_not {w : Nat} {x y : BitVec w} : ~~~x ^^^ ~~~y = x ^^^ y := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> rfl
theorem not_idemp {w : Nat} {x : BitVec w} : ~~~(~~~x) = x :=
  BitVec.not_not

theorem ult_zero_1 {n : Nat} {x : BitVec n} : (0#n < x) = ¬(x = 0#n) := by
  apply propext
  rw [BitVec.lt_def, BitVec.toNat_eq]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega
theorem ult_zero_2 {n : Nat} {x : BitVec n} : (x < 0#n) = False := by
  apply propext
  rw [BitVec.lt_def]
  simp
theorem ult_self {w : Nat} {x : BitVec w} : (x < x) = False :=
  eq_false (BitVec.lt_irrefl x)
theorem lt_self {w : Nat} {x : BitVec w} : (x.slt x = true) = False := by
  simp [BitVec.slt_iff_toInt_lt]
theorem ule_self {w : Nat} {x : BitVec w} : (x ≤ x) = True :=
  eq_true (BitVec.le_refl x)
theorem ule_zero {n : Nat} {x : BitVec n} : (x ≤ 0#n) = (x = 0#n) :=
  propext BitVec.le_zero_iff
theorem zero_ule {n : Nat} {x : BitVec n} : (0#n ≤ x) = True := by
  apply eq_true
  rw [BitVec.le_def]
  simp
theorem sle_self {w : Nat} {x : BitVec w} : (x.sle x = true) = True := by
  simp [BitVec.sle_iff_toInt_le]

theorem ule_max {w : Nat} {x : BitVec w} : (x ≤ BitVec.ofNat w (2 ^ w - 1)) = True := by
  apply eq_true
  rw [BitVec.le_def, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)]
  have := x.isLt
  omega
theorem not_ult {w : Nat} {x y : BitVec w} : (¬(x < y)) = (y ≤ x) :=
  propext BitVec.not_lt

theorem mult_pow2_1 {size : Nat} {xs ys : List (BitVec size)} {z : BitVec size}
    {n exponent u : Nat} (h₁ : n.isPowerOfTwo = True) (h₂ : exponent = n.log2)
    (h₃ : u = size - n.log2 - 1) (hn : n < 2 ^ size) :
    BitVec.mulN (xs ++ z :: BitVec.ofNat size n :: ys) =
      ((BitVec.mulN (xs ++ z :: ys)).extractLsb u 0 ++ 0#exponent).cast
        (by have := (Nat.log2_lt (Nat.ne_of_gt (Nat.pos_of_isPowerOfTwo (of_eq_true h₁)))).mpr hn
            omega) := by
  obtain ⟨k, rfl⟩ : ∃ k, _ = 2 ^ k := ⟨_, eq_two_pow_log2 h₁⟩
  rw [Nat.log2_two_pow] at h₂ h₃
  subst h₂ h₃
  have hk : exponent < size := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp hn
  rw [mulN_cons_cons_comm, ofNat_two_pow, BitVec.mul_twoPow_eq_shiftLeft, shiftLeft_nat_eq hk]
  exact shiftLeft_ofNat_eq hk (by omega)
theorem mult_pow2_2 {size : Nat} {xs ys : List (BitVec size)} {z : BitVec size}
    {n exponent u : Nat} (h₁ : (2 ^ size - n).isPowerOfTwo = True)
    (h₂ : exponent = (2 ^ size - n).log2) (h₃ : u = size - (2 ^ size - n).log2 - 1)
    (hn : 0 < n) :
    BitVec.mulN (xs ++ z :: BitVec.ofNat size n :: ys) =
      ((-BitVec.mulN (xs ++ z :: ys)).extractLsb u 0 ++ 0#exponent).cast
        (by have := (Nat.log2_lt (Nat.ne_of_gt (Nat.pos_of_isPowerOfTwo (of_eq_true h₁)))).mpr
              (Nat.sub_lt (Nat.two_pow_pos size) hn)
            omega) := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ size - n = 2 ^ k := ⟨_, eq_two_pow_log2 h₁⟩
  rw [hk, Nat.log2_two_pow] at h₂ h₃
  subst h₂ h₃
  have hk' : exponent < size :=
    (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp
      (by have := Nat.two_pow_pos size; have := Nat.two_pow_pos exponent; omega)
  rw [mulN_cons_cons_comm, ofNat_two_pow_sub hk hn, BitVec.mul_neg, ← BitVec.neg_mul,
    BitVec.mul_twoPow_eq_shiftLeft, shiftLeft_nat_eq hk']
  exact shiftLeft_ofNat_eq hk' (by omega)
theorem mult_pow2_2b {size : Nat} {z : BitVec size} {n exponent u : Nat}
    (h₁ : (2 ^ size - n).isPowerOfTwo = True) (h₂ : exponent = (2 ^ size - n).log2)
    (h₃ : u = size - (2 ^ size - n).log2 - 1) (hn : 0 < n) :
    z * BitVec.ofNat size n =
      ((-z).extractLsb u 0 ++ 0#exponent).cast
        (by have := (Nat.log2_lt (Nat.ne_of_gt (Nat.pos_of_isPowerOfTwo (of_eq_true h₁)))).mpr
              (Nat.sub_lt (Nat.two_pow_pos size) hn)
            omega) := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ size - n = 2 ^ k := ⟨_, eq_two_pow_log2 h₁⟩
  rw [hk, Nat.log2_two_pow] at h₂ h₃
  subst h₂ h₃
  have hk' : exponent < size :=
    (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp
      (by have := Nat.two_pow_pos size; have := Nat.two_pow_pos exponent; omega)
  rw [ofNat_two_pow_sub hk hn, BitVec.mul_neg, ← BitVec.neg_mul,
    BitVec.mul_twoPow_eq_shiftLeft, shiftLeft_nat_eq hk']
  exact shiftLeft_ofNat_eq hk' (by omega)

-- If the bit-vectors multiplied have enough leading zeros,
-- we can determine that the top bits of the multiplication
-- are zero and not compute them. Only apply for large bitwidths
-- as this can interfere with other mult normalization rewrites such
-- as flattening.
-- The guard `(> n 64)` and the range conditions on `x1i` and `y1i` are not needed in Lean.
theorem extract_mult_leading_bit {wx wy : Nat} {high low x1i x1in : Nat} {x2 : BitVec wx}
    {y1i y1in : Nat} {y2 : BitVec wy}
    (h : (2 * (x1in + wx) - ((if x1i = 0 then x1in else x1in - (1 + x1i.log2)) +
      (if y1i = 0 then y1in else y1in - (1 + y1i.log2))) ≤ low) = True)
    (hw : y1in + wy = x1in + wx) :
    ((BitVec.ofNat x1in x1i ++ x2) * (BitVec.ofNat y1in y1i ++ y2).cast hw).extractLsb high low =
      0#(high - low + 1) := by
  have hX := toNat_ofNat_append_lt (n := x1in) (a := x1i) (x := x2)
  have hY := toNat_ofNat_append_lt (n := y1in) (a := y1i) (x := y2)
  have hx0 : (if x1i = 0 then x1in else x1in - (1 + x1i.log2)) ≤ x1in := by split <;> omega
  have hy0 : (if y1i = 0 then y1in else y1in - (1 + y1i.log2)) ≤ y1in := by split <;> omega
  have h := of_eq_true h
  generalize (if x1i = 0 then x1in else x1in - (1 + x1i.log2)) = x0n at hX hx0 h
  generalize (if y1i = 0 then y1in else y1in - (1 + y1i.log2)) = y0n at hY hy0 h
  have hP : ((BitVec.ofNat x1in x1i ++ x2) *
      (BitVec.ofNat y1in y1i ++ y2).cast hw).toNat < 2 ^ low := by
    rw [BitVec.toNat_mul, BitVec.toNat_cast]
    calc _ ≤ (BitVec.ofNat x1in x1i ++ x2).toNat * (BitVec.ofNat y1in y1i ++ y2).toNat :=
          Nat.mod_le _ _
      _ < 2 ^ (x1in + wx - x0n) * 2 ^ (y1in + wy - y0n) := Nat.mul_lt_mul'' hX hY
      _ = 2 ^ ((x1in + wx - x0n) + (y1in + wy - y0n)) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ low := Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_zero, BitVec.getLsbD,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega))),
    Bool.and_false]

-- (a udiv 2^k) ==> 0_k a[n-1: k]
-- The condition `(> v 1)` is not needed in Lean.
theorem udiv_pow2_not_one {n : Nat} {x : BitVec n} {v power : Nat}
    (h : v.isPowerOfTwo = True) (hp : power = v.log2) (hv : v < 2 ^ n) :
    x.smtUDiv (BitVec.ofNat n v) =
      (0#power ++ x.extractLsb (n - 1) power).cast
        (by have := (Nat.log2_lt (Nat.ne_of_gt (Nat.pos_of_isPowerOfTwo (of_eq_true h)))).mpr hv
            omega) := by
  subst hp
  have hpos := Nat.pos_of_isPowerOfTwo (of_eq_true h)
  have hk : v.log2 < n := (Nat.log2_lt (Nat.ne_of_gt hpos)).mpr hv
  have hne : ¬BitVec.ofNat n v = 0 := by
    intro h'
    have h' := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at h'
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.ofNat_eq_ofNat] at h'
    omega
  rw [BitVec.smtUDiv, ite_eq_right hne, BitVec.udiv_eq, ofNat_eq_twoPow_log2 h,
    BitVec.udiv_twoPow_eq_of_lt hk, ushiftRight_nat_eq hk]
  exact lshr_by_const_1 (eq_true hk)

theorem udiv_zero {n : Nat} {x : BitVec n} : x.smtUDiv 0#n = ~~~(0#n) := by
  simp [BitVec.smtUDiv]
-- (x udiv 1) = x
theorem udiv_one {n : Nat} {x : BitVec n} : x.smtUDiv 1#n = x := by
  unfold BitVec.smtUDiv
  split
  · rename_i h
    have : n = 0 := by
      cases n with
      | zero => rfl
      | succ n => simp [BitVec.toNat_eq] at h
    subst this
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    simp only [BitVec.toNat_allOnes, Nat.pow_zero] at this ⊢
    omega
  · rw [BitVec.udiv_eq, BitVec.udiv_one]
-- (x urem 2^k) = 0_(n-k) x[k-1:0]
theorem urem_pow2_not_one {n : Nat} {x : BitVec n} {v nmp pm1 : Nat}
    (h₁ : v.isPowerOfTwo = True) (h₂ : (v > 1) = True) (h₃ : nmp = n - v.log2)
    (h₄ : pm1 = v.log2 - 1) (hv : v < 2 ^ n) :
    x % BitVec.ofNat n v =
      (0#nmp ++ x.extractLsb pm1 0).cast
        (by have h₀ := Nat.ne_of_gt (Nat.pos_of_isPowerOfTwo (of_eq_true h₁))
            have := (Nat.log2_lt h₀).mpr hv
            have := (Nat.le_log2 (k := 1) h₀).mpr (by have := of_eq_true h₂; omega)
            omega) := by
  obtain ⟨k, rfl⟩ : ∃ k, _ = 2 ^ k := ⟨_, eq_two_pow_log2 h₁⟩
  rw [Nat.log2_two_pow] at h₃ h₄
  subst h₃ h₄
  have hk : k < n := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp hv
  have hk1 : 1 ≤ k := by
    have := of_eq_true h₂
    rcases k with _ | k
    · simp at this
    · omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv, BitVec.extractLsb_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.shiftRight_zero,
    Nat.sub_zero]
  rw [Nat.sub_add_cancel hk1]

theorem urem_one {n : Nat} {x : BitVec n} : x % 1#n = 0#n :=
  BitVec.umod_one
theorem urem_self {w : Nat} {x : BitVec w} : x % x = 0#w :=
  BitVec.umod_self
-- ShiftZero rule
-- (0_k >> a) = 0_k
theorem shl_zero {n : Nat} {a : BitVec n} : 0#n <<< a = 0#n := by
  rw [BitVec.shiftLeft_eq', BitVec.zero_shiftLeft]
theorem lshr_zero {n : Nat} {a : BitVec n} : 0#n >>> a = 0#n := by
  rw [BitVec.ushiftRight_eq', BitVec.zero_ushiftRight]
theorem ashr_zero {n : Nat} {a : BitVec n} : (0#n).sshiftRight' a = 0#n := by
  rw [BitVec.sshiftRight', BitVec.zero_sshiftRight]

-- (bvugt (bvurem T x) x)
--   ==>  (ite (= x 0_k) (bvugt T x) false)
--   ==>  (and (=> (= x 0_k) (bvugt T x)) (=> (not (= x 0_k)) false))
--   ==>  (and (=> (= x 0_k) (bvugt T x)) (= x 0_k))
--   ==>  (and (bvugt T x) (= x 0_k))
--   ==>  (and (bvugt T 0_k) (= x 0_k))
theorem ugt_urem {w : Nat} {y x : BitVec w} : (y % x > x) = (x = 0#w ∧ y > 0#w) := by
  apply propext
  constructor
  · intro h
    by_cases hx : x = 0#w
    · subst hx
      rw [BitVec.umod_zero] at h
      exact ⟨rfl, h⟩
    · have : 0#w < x := by
        rw [BitVec.lt_def]; rw [BitVec.toNat_eq] at hx; simp at hx ⊢; omega
      exact absurd (BitVec.umod_lt y this) (BitVec.lt_asymm h)
  · rintro ⟨rfl, h⟩
    rw [BitVec.umod_zero]
    exact h

theorem ult_one {n : Nat} {x : BitVec n} (h : (n > 0) = True) : (x < 1#n) = (x = 0#n) :=
  propext (BitVec.lt_one_iff (of_eq_true h))

theorem merge_sign_extend_1 {w : Nat} {x : BitVec w} {i j : Nat} :
    (x.signExtend (w + j)).signExtend (w + j + i) = x.signExtend (w + j + i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro l hl
  simp only [BitVec.getLsbD_signExtend, BitVec.msb_signExtend]
  by_cases h1 : l < w
  · simp (disch := omega) only [decide_eq_true, ite_eq_left, Bool.true_and]
  · by_cases h2 : l < w + j
    · simp (disch := omega) only [decide_eq_true, ite_eq_left, ite_eq_right, Bool.true_and]
    · rcases Nat.eq_zero_or_pos (w + j) with h3 | h3
      · have hw : w = 0 := by omega
        subst hw
        simp [BitVec.msb]
      · simp (disch := omega) only [decide_eq_true, ite_eq_left, ite_eq_right, Bool.true_and]
        split
        · have : j = 0 := by omega
          subst this
          simp [BitVec.getMsbD, BitVec.msb]
        · rfl
theorem merge_sign_extend_2 {w : Nat} {x : BitVec w} {i j : Nat} (h : (j > 0) = True) :
    (x.zeroExtend (w + j)).signExtend (w + j + i) = x.zeroExtend (w + j + i) := by
  have h := of_eq_true h
  have hmsb : (x.zeroExtend (w + j)).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.zeroExtend, BitVec.getLsbD_setWidth]
    simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
    intro _
    exact BitVec.getLsbD_of_ge x _ (by omega)
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
  apply BitVec.eq_of_getLsbD_eq
  intro l hl
  simp only [BitVec.getLsbD_setWidth, BitVec.zeroExtend]
  by_cases h1 : l < w + j
  · simp (disch := omega) only [decide_eq_true, Bool.true_and]
  · simp (disch := omega) only [decide_eq_false, decide_eq_true, Bool.true_and, Bool.false_and]
    exact (BitVec.getLsbD_of_ge x _ (by omega)).symm
theorem sign_extend_eq_const_1 {w : Nat} {x : BitVec w} {m c : Nat} (hw : 0 < w) :
    (x.signExtend (w + m) = BitVec.ofNat (w + m) c) =
      (((BitVec.ofNat (w + m) c).extractLsb (w + m - 1) (w - 1) = (0#(m + 1)).cast (by omega) ∨
          (BitVec.ofNat (w + m) c).extractLsb (w + m - 1) (w - 1) =
            (~~~(0#(m + 1))).cast (by omega)) ∧
        x = ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  generalize BitVec.ofNat (w + m) c = C
  apply propext
  constructor
  · rintro rfl
    have hlast : x.getLsbD (w - 1) = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
    refine ⟨?_, ?_⟩
    · cases hmsb : x.msb
      · left
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, BitVec.getLsbD_cast,
          BitVec.getLsbD_zero, hmsb]
        split
        · obtain rfl : i = 0 := by omega
          simp [hlast, hmsb]
        · simp
      · right
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, BitVec.getLsbD_cast,
          BitVec.getLsbD_not, BitVec.getLsbD_zero, hmsb]
        split
        · obtain rfl : i = 0 := by omega
          simp [hlast, hmsb]
          omega
        · simp (disch := omega) only [decide_eq_true, Bool.true_and, Bool.not_false]
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend, BitVec.getLsbD_cast]
      simp (disch := omega) only [decide_eq_true, Nat.zero_add, ite_eq_left, Bool.true_and]
  · rintro ⟨hchi, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, ∀ j, j < m + 1 → C.getLsbD (w - 1 + j) = b := by
      rcases hchi with h | h
      · refine ⟨false, fun j hj => ?_⟩
        have := congrArg (·.getLsbD j) h
        simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast, BitVec.getLsbD_zero] at this
        simpa [show j < w + m - 1 - (w - 1) + 1 by omega] using this
      · refine ⟨true, fun j hj => ?_⟩
        have := congrArg (·.getLsbD j) h
        simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast, BitVec.getLsbD_not,
          BitVec.getLsbD_zero] at this
        simpa [show j < w + m - 1 - (w - 1) + 1 by omega, hj] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb,
      BitVec.msb_cast]
    split
    · simp (disch := omega) only [decide_eq_true, Nat.zero_add, Bool.true_and]
    · simp (disch := omega) only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb,
        decide_eq_true, Bool.true_and, Nat.zero_add, Nat.sub_zero, Nat.add_sub_cancel]
      have h1 := hb 0 (by omega)
      have h2 := hb (i - (w - 1)) (by omega)
      rw [Nat.add_zero] at h1
      rw [Nat.add_sub_cancel' (by omega)] at h2
      rw [h1, h2]
theorem sign_extend_eq_const_2 {w : Nat} {x : BitVec w} {m c : Nat} (hw : 0 < w) :
    (BitVec.ofNat (w + m) c = x.signExtend (w + m)) =
      (((BitVec.ofNat (w + m) c).extractLsb (w + m - 1) (w - 1) = (0#(m + 1)).cast (by omega) ∨
          (BitVec.ofNat (w + m) c).extractLsb (w + m - 1) (w - 1) =
            (~~~(0#(m + 1))).cast (by omega)) ∧
        x = ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  rw [← sign_extend_eq_const_1 hw]
  exact propext eq_comm
-- cvc5's bv-zero-extend-eq-const-1/2 are ill-typed as written:
-- `chi = (extract nmm1 nm1 (@bv c nm))` has `m + 1` bits but is compared with `(@bv 0 m)`.
-- These theorems state the intended rules, with `chi = (extract nmm1 n (@bv c nm))` (the top `m`
-- bits), as in cvc5's `ZeroExtendEqConst`.
theorem zero_extend_eq_const_1 {w : Nat} {x : BitVec w} {m c : Nat} (hw : 0 < w) (hm : 0 < m) :
    (x.zeroExtend (w + m) = BitVec.ofNat (w + m) c) =
      ((BitVec.ofNat (w + m) c).extractLsb (w + m - 1) w = (0#m).cast (by omega) ∧
        x = ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  generalize BitVec.ofNat (w + m) c = C
  apply propext
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_cast, BitVec.getLsbD_zero]
      rw [BitVec.getLsbD_of_ge x _ (by omega)]
      simp
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_cast]
      simp (disch := omega) only [decide_eq_true, Nat.zero_add, Bool.true_and]
  · rintro ⟨hchi, rfl⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_cast,
      BitVec.getLsbD_extractLsb]
    by_cases h : i < w
    · simp (disch := omega) only [decide_eq_true, Nat.zero_add, Bool.true_and]
    · have := congrArg (·.getLsbD (i - w)) hchi
      simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast, BitVec.getLsbD_zero] at this
      rw [Nat.add_sub_cancel' (by omega)] at this
      simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and,
        Bool.false_and] at this ⊢
      exact this.symm
theorem zero_extend_eq_const_2 {w : Nat} {x : BitVec w} {m c : Nat} (hw : 0 < w) (hm : 0 < m) :
    (BitVec.ofNat (w + m) c = x.zeroExtend (w + m)) =
      ((BitVec.ofNat (w + m) c).extractLsb (w + m - 1) w = (0#m).cast (by omega) ∧
        x = ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  rw [← zero_extend_eq_const_1 hw hm]
  exact propext eq_comm

theorem zero_extend_ult_const_1 {w : Nat} {x : BitVec w} {m c : Nat}
    (h : BitVec.ofNat (w + m) c =
      ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).zeroExtend (w + m)) (hw : 0 < w) :
    (x.zeroExtend (w + m) < BitVec.ofNat (w + m) c) =
      (x < ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  apply propext
  rw [BitVec.lt_def, BitVec.lt_def, BitVec.toNat_cast, BitVec.toNat_setWidth_of_le (by omega),
    toNat_eq_of_eq_zeroExtend hw h (by omega)]

theorem zero_extend_ult_const_2 {w : Nat} {x : BitVec w} {m c : Nat}
    (h : BitVec.ofNat (w + m) c =
      ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).zeroExtend (w + m)) (hw : 0 < w) :
    (BitVec.ofNat (w + m) c < x.zeroExtend (w + m)) =
      (((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega) < x) := by
  apply propext
  rw [BitVec.lt_def, BitVec.lt_def, BitVec.toNat_cast, BitVec.toNat_setWidth_of_le (by omega),
    toNat_eq_of_eq_zeroExtend hw h (by omega)]

theorem sign_extend_ult_const_1 {w : Nat} {x : BitVec w} {m c : Nat}
    (h : (BitVec.ofNat (w + m) c ≤ 1#(w + m) <<< BitVec.ofNat (w + m) (w - 1) ∨
      BitVec.ofNat (w + m) c ≥ ~~~(0#(w + m)) <<< BitVec.ofNat (w + m) (w - 1)) = True)
    (hw : 0 < w) :
    (x.signExtend (w + m) < BitVec.ofNat (w + m) c) =
      (x < ((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega)) := by
  have h := of_eq_true h
  generalize BitVec.ofNat (w + m) c = C at h ⊢
  apply propext
  rw [GE.ge, BitVec.le_def, BitVec.le_def, toNat_one_shiftLeft (by omega),
    toNat_allOnes_shiftLeft (by omega)] at h
  rw [BitVec.lt_def, BitVec.lt_def, BitVec.toNat_cast, toNat_signExtend_of_le (by omega),
    toNat_extractLsb_low hw, BitVec.msb_eq_decide]
  have hX := x.isLt
  have hC := C.isLt
  have hPW : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := Nat.two_pow_pred_add_two_pow_pred hw
  have hWN : 2 ^ w ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (by omega)
  have hP := Nat.two_pow_pos (w - 1)
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> omega
  · rw [mod_two_pow_of_ge (by omega) (by omega) hC]
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> omega
theorem sign_extend_ult_const_2 {w : Nat} {x : BitVec w} {m c : Nat}
    (h₁ : (1#(w + m) <<< BitVec.ofNat (w + m) (w - 1) < BitVec.ofNat (w + m) c) = True)
    (h₂ : (BitVec.ofNat (w + m) c ≤ ~~~(0#(w + m)) <<< BitVec.ofNat (w + m) (w - 1)) = True) :
    (x.signExtend (w + m) < BitVec.ofNat (w + m) c) =
      (x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega)) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  generalize BitVec.ofNat (w + m) c = C at h₁ h₂ ⊢
  apply propext
  rw [BitVec.lt_def] at h₁
  rw [BitVec.extractLsb_msb_eq_cast_iff rfl, BitVec.lt_def, toNat_signExtend_of_le (by omega),
    BitVec.msb_eq_decide, BitVec.getLsbD_zero]
  have hX := x.isLt
  have hC := C.isLt
  have hP := Nat.two_pow_pos (w - 1)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp only [Nat.pow_zero, Nat.zero_sub] at hX ⊢
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> simp [hmsb] <;> omega
  rw [toNat_one_shiftLeft (by omega)] at h₁
  rw [BitVec.le_def, toNat_allOnes_shiftLeft (by omega)] at h₂
  have hPW : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := Nat.two_pow_pred_add_two_pow_pred hw
  have hWN : 2 ^ w ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (by omega)
  split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> simp [hmsb] <;> omega
theorem sign_extend_ult_const_3 {w : Nat} {x : BitVec w} {m c : Nat}
    (h : (BitVec.ofNat (w + m) c < 1#(w + m) <<< BitVec.ofNat (w + m) (w - 1) ∨
      BitVec.ofNat (w + m) c ≥ ~~~(1#(w + m) <<< BitVec.ofNat (w + m) (w - 1))) = True)
    (hw : 0 < w) :
    (BitVec.ofNat (w + m) c < x.signExtend (w + m)) =
      (((BitVec.ofNat (w + m) c).extractLsb (w - 1) 0).cast (by omega) < x) := by
  have h := of_eq_true h
  generalize BitVec.ofNat (w + m) c = C at h ⊢
  apply propext
  rw [GE.ge, BitVec.lt_def, BitVec.le_def, BitVec.toNat_not, toNat_one_shiftLeft (by omega)] at h
  rw [BitVec.lt_def, BitVec.lt_def, BitVec.toNat_cast, toNat_signExtend_of_le (by omega),
    toNat_extractLsb_low hw, BitVec.msb_eq_decide]
  have hX := x.isLt
  have hC := C.isLt
  have hPW : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := Nat.two_pow_pred_add_two_pow_pred hw
  have hWN : 2 ^ w ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (by omega)
  have hP := Nat.two_pow_pos (w - 1)
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> omega
  · rw [mod_two_pow_of_ge (by omega) (by omega) hC]
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> omega

theorem sign_extend_ult_const_4 {w : Nat} {x : BitVec w} {m c : Nat}
    (h₁ : (~~~(~~~(0#(w + m)) <<< BitVec.ofNat (w + m) (w - 1)) ≤ BitVec.ofNat (w + m) c) = True)
    (h₂ : (BitVec.ofNat (w + m) c ≤ ~~~(1#(w + m) <<< BitVec.ofNat (w + m) (w - 1))) = True) :
    (BitVec.ofNat (w + m) c < x.signExtend (w + m)) =
      (x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega)) := by
  have h₁ := of_eq_true h₁
  have h₂ := of_eq_true h₂
  generalize BitVec.ofNat (w + m) c = C at h₁ h₂ ⊢
  apply propext
  rw [BitVec.extractLsb_msb_eq_cast_iff rfl, BitVec.lt_def, toNat_signExtend_of_le (by omega),
    BitVec.msb_eq_decide, BitVec.getLsbD_one]
  have hX := x.isLt
  have hC := C.isLt
  have hP := Nat.two_pow_pos (w - 1)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp only [Nat.pow_zero, Nat.zero_sub] at hX ⊢
    split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> simp [hmsb] <;> omega
  rw [BitVec.le_def, BitVec.toNat_not, toNat_allOnes_shiftLeft (by omega)] at h₁
  rw [BitVec.le_def, BitVec.toNat_not, toNat_one_shiftLeft (by omega)] at h₂
  have hPW : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := Nat.two_pow_pred_add_two_pow_pred hw
  have hWN : 2 ^ w ≤ 2 ^ (w + m) := Nat.pow_le_pow_right (by decide) (by omega)
  split <;> rename_i hmsb <;> simp only [decide_eq_true_eq] at hmsb <;> simp [hmsb] <;> omega

end Smt.Reconstruct.BitVec.Rewrite
