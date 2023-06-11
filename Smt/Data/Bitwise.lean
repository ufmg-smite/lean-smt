/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Bool.Basic

/-
# Bitwise Operations for Bitvectors

A bitvector is defined in BitVec as a natural number modulo 2^w (i.e. `Fin` of length 2^w). Many operators on bitvectors are defined as the corresponding operations on `Fin`. For example, less than is defined as the less than of the underlying naturals. Similarly, addition is defined as addition of the underlying naturals modulo 2^w (i.e. `Fin.add`). Many bitvector operations were defined from the [`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV) of SMT-LIBv2.

In this file, we define bitwise versions for these operations and show that they correspond to bitvector operations in BitVec.

## Main Results

* `mod_two_pow_succ` expresses a number modulo `2^(i+1)` in terms of its value modulo 2^i. This allows for induction on the most significant bit in a very clean way. This will be used extensively in the proofs of `bitwise_add` and `bitwise_mul` where induction on the most significant bit is easier.  
* `of_lt_of_testBit` shows that if `x < y` then there exists a bit `i` such that `x.testBit i = false` and `y.testBit i = true`.
* `toNat_testBit` shows that the `testBit` of `toNat` is the function at that index. This used extensively in the proof of each of the bitwise operations.
* `testBit_add` shows that `testBit` of the sum of two bitvectors is equivalent to the bitwise xor of the `testBit` of the two bitvectors and the `testBit` of the carry.

## Future Work

Prove correspondence for other bitvector operations (neg, mul, append, extract etc.). This is currently work in progress (see Bitwisemain). This is all proved but is undergoing reviews.
-/

infix:30 " ^^ " => xor

namespace Nat

lemma bit_toNat (b : Bool) : bit b 0 = b.toNat := by cases' b <;> simp

theorem two_pow_pos (w : Nat) : 0 < 2^w := Nat.pos_pow_of_pos _ (by decide)

theorem two_pow_succ (w : Nat) : 2^(w+1) = 2^w + 2^w := by simp [pow_succ, mul_two] 

lemma lt_succ_two_pow {y b i : Nat} (h: b ≤ 1) (hy : y < 2^i) : 2^i * b + y < 2^(i+1) := by 
  rw [two_pow_succ]
  exact add_lt_add_of_le_of_lt (mul_le_of_le_one_right' h) hy

lemma toNat_le_one (b: Bool) : b.toNat ≤ 1 := by cases' b <;> simp

@[simp] lemma toNat_eq_bif {b: Bool}: cond b 1 0 = b.toNat := by simp [cond, Bool.toNat]

lemma shiftr_eq_testBit : Nat.shiftr x i %2 = (x.testBit i).toNat := by simp [Nat.testBit, Nat.mod_two_of_bodd]

lemma div_add_mod_two_pow (m n : Nat) : n = 2^m*Nat.shiftr n m + n%(2^m):= by simp_rw [Nat.shiftr_eq_div_pow, Nat.div_add_mod]

/-- Useful for induction on the most significant bit.-/
theorem mod_two_pow_succ (x i : Nat) : x % 2 ^ (i+1) = 2^i * (Nat.testBit x i).toNat + x % (2^i):= by 
  have h1 := div_add_mod_two_pow i x
  have h3 := div_add_mod (Nat.shiftr x i) 2
  rw [← h3, mul_add, ←mul_assoc, ← pow_succ, shiftr_eq_testBit] at h1
  have := lt_succ_two_pow (toNat_le_one (x.testBit i)) (mod_lt x (NeZero.pos (2^i)))
  simp [(Nat.div_mod_unique (two_pow_pos (i+1))).mpr ⟨add_rotate _ _ (x%(2^i)) ▸ h1.symm, this⟩]

lemma bit_lt (h: bit b n < bit b' m) : n< m ∨ (n=m ∧ b = false ∧ b'= true) := by 
  cases' b <;> cases' b' <;> revert h
  <;> simp [le_iff_lt_or_eq]

/-- Bitblast unsigned less than.-/
def bitwise_ult (x y w : Nat) := loop x y (w - 1) 
where
  loop (x y : Nat) : Nat →  Prop
    | 0     => ¬ x.testBit 0  ∧ y.testBit 0
    | i + 1 => (¬ x.testBit (i + 1) ∧ y.testBit (i+1)) ∨ (¬(x.testBit (i + 1) ∧ ¬ y.testBit (i + 1)) ∧ loop x y i)

theorem of_lt_of_testBit (h: n<m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ ∀j, i <j → Nat.testBit m j = Nat.testBit n j := by
  induction' n using Nat.binaryRec with b n ih generalizing m
  · have ⟨i, _, _⟩ := exists_most_significant_bit (ne_of_lt h).symm
    use i; simpa [*]
  · rw [← bit_decomp m] at h ⊢
    cases' bit_lt h with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i; simp only [testBit_succ]
      exact ⟨iH.1, iH.2.1, by 
             intros j hj; cases' j with j
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (by linarith)]⟩
    · use 0; simp only [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j', hj⟩ := exists_eq_add_of_le' hj
                                 simp[hj, testBit_succ, h3.1]⟩ 

theorem lt_two_pow_testBit_false (h: x < 2^i) (h1: i ≤ j) : x.testBit j = false:= by 
  simp [testBit, shiftr_eq_div_pow, Nat.div_eq_zero (lt_of_lt_of_le h (pow_le_pow_of_le_right (by decide) h1))]

theorem testBit_true_lt_two_pow (h: x.testBit i = true) (hx : x < 2^w) : i < w := by
  by_contra'; simp [lt_two_pow_testBit_false hx this] at h

theorem bitwise_ult_of_ult (hy: y< 2^w) (h1: x < y) : bitwise_ult x y w := by
  have ⟨i, hi1, hi2, hi3⟩ := of_lt_of_testBit h1
  suffices goal: ∀ j, i+1 ≤ j → bitwise_ult x y j from goal w (testBit_true_lt_two_pow hi2 hy)
  apply le_induction
  · cases' i <;> simp [bitwise_ult, bitwise_ult.loop, hi1, hi2]
  · intros j hj ih
    have ⟨j', hj'⟩ := exists_eq_add_of_le' (le_of_add_le_right hj)
    simp only [bitwise_ult, bitwise_ult.loop, hj', succ_sub_one j'] at ih ⊢ 
    simp [ih, hi3 (j'+1) (by linarith)]

theorem bodd_eq_mod_two : bodd x = bodd y ↔ x % 2 = y % 2 := by
  cases' hx : bodd x <;> cases' hy : bodd y 
  <;> simp [mod_two_of_bodd, hx ,hy]

theorem testBit_translate {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w* b + x) i := by
  simp only [testBit, shiftr_eq_div_pow, bodd_eq_mod_two]
  rw [Nat.add_div_of_dvd_right (by simp [Dvd.dvd.mul_right, pow_dvd_pow, le_of_lt h]), add_mod]
  have h1: (2^w/2^i)%2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero]
    use 2^(w-(i+1))
    rw [Nat.pow_div (by linarith) (by decide), mul_comm, ← pow_succ 2 _, succ_eq_add_one]
    simp [← Nat.sub_add_comm, succ_le_of_lt h]
  simp [mul_comm, Nat.mul_div_assoc b (pow_dvd_pow 2 (le_of_lt h)), mul_mod, h1]

theorem testBit_translate' {x w :Nat} {b:Bool} (h: x<2^w) : Nat.testBit (2^w*b.toNat + x) w = b:= by
  simp only [Nat.testBit, Nat.shiftr_eq_div_pow]
  rw [Nat.add_div_of_dvd_right (Dvd.intro _ rfl), Nat.div_eq_zero h, add_zero]
  cases' b <;> simp 

@[simp] lemma toNat_true : true.toNat = 1 := rfl

theorem testBit_translate_one {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w+ x) i := mul_one (2^w) ▸ (@testBit_translate 1 _ _ _ h)

theorem testBit_translate_one' {x w :Nat} (h: x<2^w) : Nat.testBit (2^w+x) w = true:= mul_one (2^w) ▸ toNat_true ▸ (@testBit_translate' x w true h)

@[simp] lemma testBit_bool : testBit b.toNat 0 = b := by cases' b <;> simp

/---Generic method to create a natural number by tail-recursively appending bits from the tail. This is an alternative to using `List` altogether.-/
def toNat (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => z.bit (f 0)
  | i + 1 => toNat f (z.bit (f (i + 1))) i

theorem toNat_succ {f : Nat → Bool}: toNat f z i = 2^(i+1)*z + toNat f 0 i := by
  induction' i with i ih generalizing z
  · simp [toNat, bit_val]
  · simp only [toNat, @ih (bit (f (i+1)) 0), @ih (bit (f (i+1)) z)]
    rw [bit_val, mul_add, ← mul_assoc, ← pow_succ]
    simp [bit_val, add_assoc] 

theorem toNat_lt {f: Nat → Bool} : toNat f 0 i < 2^(i+1) := by
  induction' i with i ih
  · simp [toNat, bit_val, lt_succ, toNat_le_one]
  · simp only [toNat]
    rw [toNat_succ]
    cases' (f (i+1)) <;> simp [ih, two_pow_succ] at * <;> linarith

/--The `ith` bit of `toNat` is the function at `i`.-/
theorem toNat_testBit {f: Nat → Bool} (h1: i ≤ j): (toNat f 0 j).testBit i = f i := by
  induction' j with j ih generalizing i
  · simp [nonpos_iff_eq_zero.mp h1, toNat, bit_val]
  · cases' lt_or_eq_of_le h1 with h1 h1
    · rw [← ih (show i ≤ j by linarith), toNat, toNat_succ, ←testBit_translate h1]
    · rw [h1, toNat, toNat_succ, bit_toNat, testBit_translate' (toNat_lt)]

/---Carry function for bitwise addition.-/
def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

/---Bitblast addition-/
@[simp] def bitwise_add (x y i: Nat) := toNat (λ j => (x.testBit j ^^ y.testBit j) ^^ bitwise_carry x y j) 0 i

lemma unfold_carry (x y i : Nat) : (bitwise_carry x y (i+1)).toNat = ((Nat.testBit x i && Nat.testBit y i) || ((Nat.testBit x i ^^ Nat.testBit y i) && bitwise_carry x y i)).toNat := by simp [bitwise_carry]

theorem bitwise_add_eq_add_base (x y i: Nat) : x%(2^(i+1)) + y%(2^(i+1)) = bitwise_add x y i + 2^(i+1)*(bitwise_carry x y (i+1)).toNat := by
  induction' i with i hi
  · simp only [bitwise_carry, bitwise_add, toNat]
    cases' hx: Nat.bodd x  <;> cases' hy: Nat.bodd y
    <;> simp [mod_two_of_bodd, testBit, hx, hy, shiftr]
  · rw [mod_two_pow_succ x, mod_two_pow_succ y]
    rw [add_assoc, add_comm _ (y % 2 ^ (i + 1)), ← add_assoc (x % 2 ^ (i + 1))]
    rw [hi, unfold_carry x y (succ i), two_pow_succ (succ i)]
    cases' hx : Nat.testBit x (i+1) <;> cases' hy : Nat.testBit y (i+1) 
    <;> cases' hc : bitwise_carry x y (i+1) 
    <;> simp [Bool.toNat, @toNat_succ 1 i _, two_pow_succ, hx, hy, hc, toNat]
    <;> ring

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y i = (x + y) % 2 ^ (i + 1) := by
  rw [Nat.add_mod, bitwise_add_eq_add_base]
  cases' i with i i
  · cases' h0: Nat.testBit x 0 ^^ (Nat.testBit y 0 ^^ bitwise_carry x y 0)
    <;> simp [toNat, h0]
  · simp [bitwise_add, Nat.mod_eq_of_lt toNat_lt]

theorem testBit_add {x y i: Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ bitwise_carry x y i):= by
  have := lt_of_lt_of_le (lt_trans (lt_two_pow (x + y)) (pow_lt_pow_succ (by decide) (x + y))) (pow_le_pow_of_le_right (show 0 < 2 by decide) (@le_add_self _ _ _ i))
  rw [← Nat.mod_eq_of_lt this, ← add_assoc, ← bitwise_add_eq_add x y]
  simp [toNat_testBit (show i ≤ i + (x + y) by linarith)]

end Nat