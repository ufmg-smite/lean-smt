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

-- https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites-elimination

private theorem xor_iff_iff_not {p q : Prop} : XOr p q ↔ (p ↔ ¬q) := by
  constructor
  · intro h
    cases h with
    | inl hp hq => exact ⟨fun _ => hq, fun _ => hp⟩
    | inr hp hq => exact ⟨fun h => absurd h hp, fun h => absurd hq h⟩
  · intro h
    by_cases hp : p
    · exact XOr.inl hp (h.mp hp)
    · exact XOr.inr hp (Classical.byContradiction fun hq => hp (h.mpr hq))

private theorem testBit_eq_decide_le {m n : Nat} (h : m < 2 ^ (n + 1)) :
    m.testBit n = decide (2 ^ n ≤ m) := by
  rw [Nat.pow_succ] at h
  by_cases hm : m < 2 ^ n
  · rw [Nat.testBit_lt_two_pow hm]; simp; omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = 2 ^ n + k := ⟨m - 2 ^ n, by omega⟩
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
    simp

private theorem intMin_eq_cast {n w : Nat} (h : 1 + n = w) :
    BitVec.intMin w = (1#1 ++ 0#n).cast h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_intMin, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_zero]
  split
  · simp; omega
  · simp; omega

-- Operator Elimination Rules

theorem ugt_eliminate {w : Nat} {x y : BitVec w} : (x > y) = (y < x) := rfl
theorem uge_eliminate {w : Nat} {x y : BitVec w} : (x ≥ y) = (y ≤ x) := rfl
theorem sgt_eliminate {w : Nat} {x y : BitVec w} : (y.slt x = true) = (y.slt x = true) := rfl
theorem sge_eliminate {w : Nat} {x y : BitVec w} : (y.sle x = true) = (y.sle x = true) := rfl
theorem sle_eliminate {w : Nat} {x y : BitVec w} : (x.sle y = true) = ¬(y.slt x = true) := by
  rw [BitVec.sle_eq_not_slt]; simp

theorem redor_eliminate {w : Nat} {x : BitVec w} : x.smtRedor = ~~~(x.smtComp (0#w)) := by
  unfold BitVec.smtRedor BitVec.smtComp
  split <;> decide
theorem redand_eliminate {w : Nat} {x : BitVec w} : x.smtRedand = x.smtComp (~~~(0#w)) := by
  rw [BitVec.not_zero]; rfl

theorem ule_eliminate {w : Nat} {x y : BitVec w} : (x ≤ y) = ¬(y < x) :=
  propext BitVec.not_lt.symm
theorem comp_eliminate {w : Nat} {x y : BitVec w} :
    x.smtComp y = if x = y then 1#1 else 0#1 := rfl

theorem rotate_left_eliminate_1 {w : Nat} {x : BitVec w} {amount : Nat}
    (h : (amount % w = 0) = False) (hw : 0 < w) :
    x.rotateLeft amount =
      (x.extractLsb (w - (1 + amount % w)) 0 ++ x.extractLsb (w - 1) (w - amount % w)).cast
        (by have := of_eq_false h; have := Nat.mod_lt amount hw; omega) := by
  have ha := Nat.mod_lt amount hw
  have ha0 := of_eq_false h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb]
  generalize amount % w = a at *
  rw [show w - 1 - (w - a) + 1 = a by omega, show w - (1 + a) - 0 + 1 = w - a by omega]
  by_cases hia : i < a
  · simp [hia]
  · simp [hia, hi, show i - a < w - a by omega]
theorem rotate_left_eliminate_2 {w : Nat} {x : BitVec w} {amount : Nat} (h : amount % w = 0) :
    x.rotateLeft amount = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [h, hi]
theorem rotate_right_eliminate_1 {w : Nat} {x : BitVec w} {amount : Nat}
    (h : (amount % w = 0) = False) (hw : 0 < w) :
    x.rotateRight amount =
      (x.extractLsb (amount % w - 1) 0 ++ x.extractLsb (w - 1) (amount % w)).cast
        (by have := of_eq_false h; have := Nat.mod_lt amount hw; omega) := by
  have ha := Nat.mod_lt amount hw
  have ha0 := of_eq_false h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb]
  generalize amount % w = a at *
  rw [show w - 1 - a + 1 = w - a by omega, show a - 1 - 0 + 1 = a by omega]
  by_cases hia : i < w - a
  · simp [hia]
  · simp [hia, hi, show i - (w - a) < a by omega]
theorem rotate_right_eliminate_2 {w : Nat} {x : BitVec w} {amount : Nat} (h : amount % w = 0) :
    x.rotateRight amount = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [h, hi]

theorem nand_eliminate {w : Nat} {x y : BitVec w} : x.smtNand y = ~~~(x &&& y) := rfl
theorem nor_eliminate {w : Nat} {x y : BitVec w} : x.smtNor y = ~~~(x ||| y) := rfl
theorem xnor_eliminate {w : Nat} {x y : BitVec w} : x.smtXnor y = ~~~(x ^^^ y) := rfl

theorem sdiv_eliminate {w : Nat} {x y : BitVec w} :
    x.smtSDiv y =
      if XOr (x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega))
          (y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega)) then
        -((if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -x else x).smtUDiv
          (if y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -y else y))
      else
        (if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -x else x).smtUDiv
          (if y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -y else y) := by
  simp only [BitVec.extractLsb_msb_eq_one_iff rfl, xor_iff_iff_not, BitVec.smtSDiv_eq]
  cases x.msb <;> cases y.msb <;> simp

theorem zero_extend_eliminate {w : Nat} {x : BitVec w} {n : Nat} :
    x.zeroExtend (w + n) = (0#n ++ x).cast (by omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_zero]
  split
  · simp; omega
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact .inr (BitVec.getLsbD_of_ge x i (by omega))

theorem uaddo_eliminate {w : Nat} {x y : BitVec w} :
    (x.uaddOverflow y = true) =
      (((0#1 ++ x) + (0#1 ++ y)).extractLsb w w = (1#1).cast (by omega)) := by
  rw [BitVec.extractLsb_eq_one_iff, ← BitVec.testBit_toNat, BitVec.toNat_add, BitVec.toNat_append,
    BitVec.toNat_append]
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have hp : 2 ^ (1 + w) = 2 * 2 ^ w := by rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
  rw [Nat.mod_eq_of_lt (by omega), testBit_eq_decide_le (by rw [Nat.pow_succ]; omega)]
  simp [BitVec.uaddOverflow]
theorem saddo_eliminate {w : Nat} {x y : BitVec w} :
    (x.saddOverflow y = true) =
      (((x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) ∧
            y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega)) ∧
          (x + y).extractLsb (w - 1) (w - 1) = (0#1).cast (by omega)) ∨
        ((x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) ∧
            y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega)) ∧
          (x + y).extractLsb (w - 1) (w - 1) = (1#1).cast (by omega))) := by
  simp only [BitVec.extractLsb_msb_eq_one_iff rfl, BitVec.extractLsb_msb_eq_zero_iff rfl,
    BitVec.saddOverflow_eq]
  cases x.msb <;> cases y.msb <;> cases (x + y).msb <;> simp
theorem sdivo_eliminate {w : Nat} {x y : BitVec w} (hw : 0 < w) :
    (x.sdivOverflow y = true) = (x = (1#1 ++ 0#(w - 1)).cast (by omega) ∧ y = ~~~(0#w)) := by
  rw [BitVec.sdivOverflow_eq, ← intMin_eq_cast, BitVec.not_zero]
  simp [hw]
theorem smod_eliminate {w : Nat} {x y : BitVec w} :
    x.smod y =
      if (if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y) = 0#w then
        (if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y)
      else if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) ∧
          y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then
        (if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y)
      else if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) ∧
          y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then
        -((if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y)) + y
      else if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) ∧
          y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then
        (if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y) + y
      else
        -((if x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then x else -x) %
          (if y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) then y else -y)) := by
  simp only [BitVec.extractLsb_msb_eq_one_iff rfl, BitVec.extractLsb_msb_eq_zero_iff rfl,
    BitVec.smod_eq, BitVec.umod_eq]
  cases x.msb <;> cases y.msb <;> simp
  · rw [BitVec.sub_eq_add_neg, BitVec.add_comm y]
  · intro hu
    rw [hu, BitVec.neg_zero]

theorem srem_eliminate {w : Nat} {x y : BitVec w} :
    x.srem y =
      if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then
        -((if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -x else x) %
          (if y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -y else y))
      else
        (if x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -x else x) %
          (if y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) then -y else y) := by
  simp only [BitVec.extractLsb_msb_eq_one_iff rfl, BitVec.srem_eq]
  cases x.msb <;> cases y.msb <;> simp

theorem usubo_eliminate {n : Nat} {x y : BitVec n} :
    (x.usubOverflow y = true) =
      ((x.zeroExtend (n + 1) - y.zeroExtend (n + 1)).extractLsb n n = (1#1).cast (by omega)) := by
  have hx := x.isLt
  have hy := y.isLt
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hx' : (x.zeroExtend (n + 1)).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hy' : (y.zeroExtend (n + 1)).toNat = y.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.usubOverflow_eq, BitVec.extractLsb_eq_one_iff, ← BitVec.testBit_toNat]
  by_cases hxy : x.toNat < y.toNat
  · rw [BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def, hx', hy']; exact hxy), hx', hy',
      testBit_eq_decide_le (by omega)]
    simp [BitVec.lt_def, hxy]
    omega
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx', hy']; omega), hx', hy',
      Nat.testBit_lt_two_pow (by omega)]
    simp [BitVec.lt_def, hxy]
theorem ssubo_eliminate {w : Nat} {x y : BitVec w} :
    (x.ssubOverflow y = true) =
      (((x.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega) ∧
            y.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega)) ∧
          (x - y).extractLsb (w - 1) (w - 1) = (0#1).cast (by omega)) ∨
        ((x.extractLsb (w - 1) (w - 1) = (0#1).cast (by omega) ∧
            y.extractLsb (w - 1) (w - 1) = (1#1).cast (by omega)) ∧
          (x - y).extractLsb (w - 1) (w - 1) = (1#1).cast (by omega))) := by
  simp only [BitVec.extractLsb_msb_eq_one_iff rfl, BitVec.extractLsb_msb_eq_zero_iff rfl,
    BitVec.ssubOverflow_eq]
  cases x.msb <;> cases y.msb <;> cases (x - y).msb <;> simp

theorem nego_eliminate {w : Nat} {x : BitVec w} (hw : 0 < w) :
    (x.negOverflow = true) = (x = (1#1 ++ 0#(w - 1)).cast (by omega)) := by
  rw [BitVec.negOverflow_eq, ← intMin_eq_cast]
  simp [hw]

end Smt.Reconstruct.BitVec.Rewrite
