/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed, Wojciech Nawrocki, Joe Hendrix
-/

import Std
import Smt.Data.Bitwise


/-!
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w}`, `Fin w → Bool`.

We also define many bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIBv2.

TODO(WN): This is planned to go into mathlib4 once we:
  - have sorry-free bound proofs
  - match the interface to what SMT-LIB provides
  - are otherwise happy with the API
-/

/-- A bitvector of the specified width. This is represented as the underlying `Nat` number
in both the runtime and the kernel, inheriting all the special support for `Nat`. -/

def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

namespace BitVec

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.two_pow_pos w⟩

/-- The bitvector `n mod 2^w`. -/
protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (Nat.two_pow_pos w)

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

-- We inherit `Fin` implementations when fast but write mod/div
-- ourselves to avoid the extra modulo operation.
protected def add (x y : BitVec w) : BitVec w := Fin.add x y
protected def sub (x y : BitVec w) : BitVec w := Fin.sub x y
protected def mul (x y : BitVec w) : BitVec w := Fin.mul x y
protected def neg (x : BitVec w) : BitVec w := (Fin.neg (2^w)).neg x

protected def mod (x y : BitVec w) : BitVec w :=
  ⟨x.val % y.val, Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt⟩
protected def div (x y : BitVec w) : BitVec w :=
  ⟨x.val / y.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt⟩
--when y=0 its the bitvectors of all 1s
protected def lt (x y : BitVec w) : Bool :=
  x.val < y.val
protected def le (x y : BitVec w) : Bool :=
  x.val ≤ y.val

instance : Add (BitVec w) := ⟨BitVec.add⟩
instance : Sub (BitVec w) := ⟨BitVec.sub⟩
instance : Mul (BitVec w) := ⟨BitVec.mul⟩
instance : Mod (BitVec w) := ⟨BitVec.mod⟩
instance : Div (BitVec w) := ⟨BitVec.div⟩
instance : LT (BitVec w)  := ⟨fun x y => BitVec.lt x y⟩
instance : LE (BitVec w)  := ⟨fun x y => BitVec.le x y⟩


@[norm_cast, simp]
theorem val_bitvec_eq {a b : BitVec w} : a.val = b.val ↔ a = b :=
  ⟨(match a, b, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
-- why is this a simp lemma?
@[norm_cast, simp]
theorem val_bitvec_lt {a b : BitVec w} : (a.val : ℕ) < (b.val : ℕ) ↔ a < b := by
  simp [LT.lt, BitVec.lt]

/-- `a ≠ b` as natural numbers if and only if `a != b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_bitvec_bne {a b : BitVec w} : a.val ≠ b.val ↔ a != b := by
  simp [bne]

protected def complement (x : BitVec w) : BitVec w :=
  0 - (x + .ofNat w 1)

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, by simp [HAnd.hAnd, AndOp.and, Nat.land, Nat.bitwise_lt]⟩ -- why do i have to unfold everything?

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, by simp [HOr.hOr, OrOp.or, Nat.lor, Nat.bitwise_lt]⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, by simp [HXor.hXor, Xor.xor, Nat.xor, Nat.bitwise_lt]⟩

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  .ofNat w (x.val <<< n)

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, by 
      simp only [Nat.shiftRight_eq_shiftr, Nat.shiftr_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self' _ _) (x.isLt) ⟩ 

instance : Complement (BitVec w) := ⟨BitVec.complement⟩
instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

def rotateLeft (x : BitVec w) (n : Nat) : BitVec w :=
  x <<< n ||| x >>> (w - n)

def rotateRight (x : BitVec w) (n : Nat) : BitVec w :=
  x >>> n ||| x <<< (w - n)

protected def append (x : BitVec w) (y : BitVec v) : BitVec (w+v) :=
  ⟨x.val <<< v ||| y.val, Nat.add_comm _ _ ▸ Nat.concat_size y.isLt x.isLt⟩ -- is it swapped? why?

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) := ⟨BitVec.append⟩

@[simp] def extract (i j : Nat) (x : BitVec w) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (x.val >>> j)

def repeat_ : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ repeat_ n x)

def zeroExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : w+i = i+w := Nat.add_comm _ _
  hEq ▸ ((0 : BitVec i) ++ x)

def signExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : ((w-1) - (w-1) + 1)*i + w = w+i := by
    rw [Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.add_comm]
  hEq ▸ ((repeat_ i (extract (w-1) (w-1) x)) ++ x)

-- `prefix` may be a better name
def shrink (v : Nat) (x : BitVec w) : BitVec v :=
  if hZero : 0 < v then
    have hEq : v - 1 + 0 + 1 = v := by
      rw [Nat.add_zero]
      exact Nat.sub_add_cancel hZero
    hEq ▸ x.extract (v - 1) 0
  else 0

/-- Return the `i`-th least significant bit. -/
@[simp] def lsbGet (x : BitVec w) (i : Nat) : Bool :=
  x.extract i i != 0

theorem lsbGet_eq_testBit {x : BitVec w} : x.lsbGet i = x.val.testBit i := by
  cases' h: Nat.bodd (Nat.shiftr (x.val) i)
  <;> simp [Nat.testBit, BitVec.ofNat, Fin.ofNat', h, Nat.mod_two_of_bodd, Nat.shiftRight, Nat.shiftRight_eq_shiftr] --probably some API missing here.. shouldnt have to take cases
  aesop-- non-terminating simp :(

instance : GetElem (BitVec w) Nat Bool (fun _ i => i < w) where
  getElem x i _ := Nat.testBit x.val i

@[simp] lemma bit_0 (b : Bool) : Nat.bit b 0 = b.toNat := by
  cases' b <;> simp

@[simp] lemma bit_1 (b : Bool) (_ : Nat) : Nat.bit b 1 = 2+b.toNat:= by
  cases' b <;> simp

open Nat

theorem bV_extract {x : BitVec w} : bitwise_extract x.val i j = (extract i j x).val := by
  simp [bitwise_extract_eq_extract, BitVec.ofNat, Fin.ofNat']

theorem bV_concat {x : BitVec w} {y : BitVec v} (h: 0 < v): (x ++ y).val = bitwise_concat y.val x.val v w := by
  simp [HAppend.hAppend, BitVec.append, bitwise_concat_eq_concat h y.isLt x.isLt]

@[simp] lemma unfold_bitwise_ext : bitwise_ext x n k = bitwise_ext.go x (n-1) 0 (n+k-1) := rfl

lemma testBit_eq_ofNat {x: BitVec w} : Bool.toNat (testBit (x.val) k) = (BitVec.ofNat 1 (x.val >>> k)).val:= by
  simp only [BitVec.ofNat, Fin.ofNat', testBit, shiftRight_eq_shiftr, mod_two_of_bodd, pow_one]
  aesop

lemma val_to_ofNat (h: m < 2^w) : (BitVec.ofNat w m).val = m := by simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt h]

lemma ofNat_to_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt x.isLt]

lemma ofNat_to_val' (x : BitVec w) (h : v = w): HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_to_val x).symm

theorem bv_concat_ext {x : BitVec a} {y : BitVec b} :
  (x ++ y).val = x.val <<< b ||| y.val := rfl

--should we use `shiftr_eq_div_pow` or not?
theorem bv_extract_ext : (extract i j x).val = x.val/2^j % (2^(i - j + 1)) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_shiftr, shiftr_eq_div_pow]

lemma bVappend_eq_add {x: BitVec w} {y : BitVec v} : (x ++ y).val = x.val * 2^v + y.val := by
  simp only [HAppend.hAppend, BitVec.append, BitVec.val_bitvec_eq, append_eq_add y.isLt, mul_comm]

--this was a private lemma but had to use it for rewrite rules
lemma cast_heq {x : BitVec w} (h: w=v) : (h ▸ x).val = x.val := by
  rw [← val_to_ofNat (show x.val < 2^v from (h.symm ▸ x.isLt)), BitVec.val_bitvec_eq]
  exact eq_of_heq (rec_heq_iff_heq.mpr (ofNat_to_val' _ h.symm)) 

lemma signExtend_succ {x: BitVec w} (h: 0 < w) : (signExtend (succ i) x).val =  (signExtend i x).val + 2 ^ (i+w) * Bool.toNat (testBit (x.val) (w - 1)) := by
  simp only [signExtend, cast_heq, bVappend_eq_add, repeat_, extract]
  rw [show w - 1 - (w - 1) + 1 = 1 by simp]
  simp [cast_heq, testBit_eq_ofNat, add_mul, mul_assoc, ← pow_add, add_rotate _ _ x.val, mul_comm _ (2^(i+w))]

lemma signExtend_zero {x: BitVec w} (_: 0 < w) : (signExtend 0 x).val = x.val := by
  simp [signExtend, cast_heq, bVappend_eq_add, repeat_, extract]

theorem bv_signExtend {x : BitVec w} (h: 0 < w): (signExtend i x).val = bitwise_ext x.val w i := by
  induction' i with i ih 
  · rw [signExtend_zero h, bitwise_ext_zero h x.isLt]
  · rw [unfold_bitwise_ext] at *
    rw [show w+ succ i -1 = w + i - 1 + 1 by simp [sub_add_comm, Nat.sub_add_cancel (show 1 ≤ w + i by linarith)]]
    simp only [bitwise_ext.go, bit_0]
    rw [bitwise_ext_succ, @bitwise_ext_succ _ _ (Bool.toNat (testBit (x.val) (w - 1))) _]
    rw [Nat.sub_add_cancel (show 1 ≤ w+ i by linarith)]
    simp only [← ih, (show ¬ w+i < w-1 by simp_arith), ite_false, add_comm (2 ^ (w + i) * Bool.toNat (testBit (x.val) (w - 1))) _] -- this add_comm super long
    simp [signExtend_succ h, Nat.sub_add_cancel (show 1 ≤ i+ w by linarith), add_comm w i, ih]   
-- if use bitvec = bitvec version then make another lemma that reduces it to the .val version above (so that you dont reprove it every single time)

theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = testBit x.val i := by rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w): (BitVec.ofNat w x)[i] = testBit x i := by 
  simp [BitVec.ofNat, GetElem.getElem, lsbGet, extract, Fin.ofNat', mod_eq_of_lt, h2]

theorem ult {x y : BitVec w} (h1: x < y) : bitwise_ult x.val y.val w:= bitwise_ult_of_ult y.isLt (val_bitvec_lt.mpr h1)


-- alternative toNat definition that uses lists
-- def toNat' (bs : List Bool) : Nat := List.foldr Nat.bit 0 bs

-- lemma toNat'_lt : toNat' bs < 2^bs.length := by
--   simp only [toNat']
--   induction' bs with b l ih
--   · simp
--   · simp only [List.foldr, bit_val, List.length_cons]
--     cases' b <;> simp [two_pow_succ, two_mul (List.foldr bit 0 l)] at * <;> linarith [ih] 

-- def bbT' (bs : List Bool): BitVec bs.length :=
--   ⟨toNat' bs, toNat'_lt⟩

def bbT (bs : List Bool) (h: 0 < bs.length): BitVec bs.length :=
  ⟨toNat (λ i => bs[i]!) 0 (bs.length - 1), by 
  apply Eq.trans_gt _ (@toNat_lt _ _); simp [Nat.sub_add_cancel h]⟩

end BitVec
