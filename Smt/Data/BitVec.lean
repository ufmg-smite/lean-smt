/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Joe Hendrix, Harun Khan, Abdalrhman M Mohamed,
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

/- ### Definitions -/

def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

namespace BitVec

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.two_pow_pos w⟩

lemma isLt (x : BitVec w) : x.val < 2^w := by simp

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
--when `y = 0` its the bitvectors of all `1s`
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
instance : Neg (BitVec w) := ⟨BitVec.neg⟩

@[norm_cast, simp]
theorem val_bitvec_eq {a b : BitVec w} : a.val = b.val ↔ a = b :=
  ⟨(match a, b, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
-- why is this a simp lemma?
@[norm_cast, simp]
theorem val_bitvec_lt {a b : BitVec w} : (a.val : ℕ) < (b.val : ℕ) ↔ a < b := by
  simp [LT.lt, BitVec.lt]

@[norm_cast, simp]
theorem val_bitvec_beq {a b : BitVec w} : (a.val == b.val) ↔ (a == b) := by simp

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
  ⟨x.val <<< v ||| y.val, Nat.add_comm _ _ ▸ Nat.append_lt y.isLt x.isLt⟩ -- is it swapped? why?

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

/-- Return the `i`-th least significant bit or `false` if `i ≥ w`. -/
@[inline] def getLsb : BitVec w -> Nat -> Bool | ⟨x,_⟩, i => x.testBit i

/-- Return the `i`-th most significant bit or `false` if `i ≥ w`. -/
@[inline] def getMsb (x : BitVec w) (i : Nat) : Bool := i < w && getLsb x (w-1-i)

/-- Return most-significant bit in bitvector. -/
@[inline] def msb (a : BitVec n) : Bool := getMsb a 0

/-- Interpret the bitvector as an integer stored in two's complement form. -/
def toInt (a : BitVec n) : Int :=
  if msb a then Int.ofNat a.val - Int.ofNat (2^n) else a.val

protected def slt (x y : BitVec n) : Bool := x.toInt < y.toInt

-- alternative defn
-- protected def slt' (x y : BitVec (w + 1)) : Prop :=
--   x + BitVec.ofNat (w + 1) (2^w) < y + BitVec.ofNat (w + 1) (2^w)

protected def sle (x y : BitVec n) : Bool := x.toInt ≤ y.toInt

-- alternative defn
-- protected def sle' (x y : BitVec (w + 1)) : Prop :=
--   ¬ (BitVec.slt' y x)

protected def sgt (x y : BitVec (w + 1)) : Prop := BitVec.slt y x

protected def sge (x y : BitVec (w + 1)) : Prop := BitVec.sle y x

def bv_xnor (x y : BitVec w) : BitVec w := (x &&& y) ||| (~~~x &&& ~~~y)

def bv_comp (x y : BitVec w) : BitVec 1 := BitVec.ofNat 1 ((decide (x = y)).toNat)

--define it this way?
def bv_redor (x w : Nat) := BitVec.ofNat 1 (helper w).toNat where
  helper : Nat → Bool
  | 0 => false
  | i + 1 => (x.testBit i) || (helper i)

--define it this way?
def bv_redand (x w : Nat) := BitVec.ofNat 1 (helper w).toNat where
  helper : Nat → Bool
  | 0 => true
  | i + 1 =>  (x.testBit i) && (helper i)

def bv_nand (x y : BitVec w) := ~~~ (x &&& y)

def bv_nor (x y : BitVec w) := ~~~ (x ||| y)

def sdiv (s t : BitVec n) : BitVec n :=
  match s.msb, t.msb with
  | false, false =>  s/t
  | false, true  => - (s / (-t))
  | true,  false => - ((- s) / t)
  | true,  true  => (- s) / (- t)

def smod (s t : BitVec m) : BitVec m :=
  match s.msb, t.msb with
  | false, false => s % t
  | false, true =>
    let u := s % (-t)
    (if u = BitVec.ofNat m 0 then u else u + t)
  | true, false =>
    let u := (-s) % t
    (if u = BitVec.ofNat m 0 then u else t - u)
  | true, true => -((-s) % (-t))

def srem (s t : BitVec n) : BitVec n :=
  match s.msb, t.msb with
  | false, false => s % t
  | false, true  => s % (-t)
  | true,  false => -((-s) % t)
  | true,  true  => -((-s) % (-t))

-- def bv_ite (c : BitVec 1) (t e : BitVec w) :=
--   BitVec.ofNat w (toNat (fun i => ((!(c.val.testBit 0)) || (t.val.testBit i)) && ((c.val.testBit 0) || (e.val.testBit i))) 0 w)
protected def ite (c : BitVec 1) (t e : BitVec w) := if msb c then t else e

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

def bbT (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.toNat (λ i => bs[i]!) 0 bs.length, @Nat.toNat_lt (bs.length) _⟩



/-! ### Lemmas -/

open Nat

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

--this is weird
lemma testBit_eq_ofNat {x: BitVec w} : Bool.toNat (testBit (x.val) k) = (BitVec.ofNat 1 (x.val >>> k)).val:= by
  simp only [BitVec.ofNat, Fin.ofNat', testBit, shiftRight_eq_shiftr, mod_two_of_bodd, pow_one]
  aesop

lemma val_to_ofNat (h: m < 2^w) : (BitVec.ofNat w m).val = m := by simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt h]

lemma ofNat_to_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt x.isLt]

lemma ofNat_to_val' (x : BitVec w) (h : v = w): HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_to_val x).symm

@[simp] lemma length_zero_eq_zero {x : BitVec 0} : x = 0 := by simp [← val_bitvec_eq]

@[simp] lemma zero_cast : (0 : BitVec w).val = 0 := rfl


lemma lt_cast {x y : BitVec w} : (x < y) = decide (x.val < y.val) := rfl

lemma add_cast {x y : BitVec w} :  (x + y).val = (x.val + y.val) % 2^w := rfl

lemma neg_cast {x : BitVec w} : (-x).val = (2^w - x.val) % 2^w := rfl

lemma sub_cast {x y : BitVec w} : (x - y).val = (x.val + (2^w - y.val)) % 2^w := rfl

lemma not_cast {x : BitVec w} : (~~~ x).val = (2^w - (x.val + 1) % 2^w) % 2^w := by
  cases' w with w
  · simp
  · simp [Complement.complement, BitVec.complement, sub_cast, add_cast, val_to_ofNat (one_lt_two_pow _ (succ_pos w))]

@[simp] lemma zero_eq_ofNat : BitVec.ofNat w 0 = (0 : BitVec w)  := rfl

@[simp] protected lemma neg_zero : -(0 : BitVec w) = 0 := by
  rw [← val_bitvec_eq, neg_cast]; simp

lemma bvneg_add_eq_sub {x y : BitVec w} : -x + y = y - x := by
  rw [← val_bitvec_eq]
  simp only [add_cast, neg_cast, sub_cast]
  cases' x.val
  · simp
  · rw [mod_eq_of_lt (sub_lt (two_pow_pos w) (succ_pos _))]; ring_nf

@[simp] lemma not_zero : (~~~(0 : BitVec w)).val = 2^w - 1 := by
  cases' w with w
  <;> simp [not_cast, one_mod_lt (one_lt_two_pow' _), mod_eq_of_lt (sub_lt (two_pow_pos _) (Nat.one_pos))]

lemma concat_cast {x : BitVec a} {y : BitVec b} :
  (x ++ y).val = x.val <<< b ||| y.val := rfl

lemma or_cast {x y : BitVec w} :
  (x ||| y).val = x.val ||| y.val := rfl

lemma and_cast {x y : BitVec w} : (x &&& y).val = x.val &&& y.val := rfl

lemma xor_cast {x y : BitVec w} : (x ^^^ y).val = x.val ^^^ y.val := rfl

lemma rem_cast {x y : BitVec w} : (x % y).val = x.val % y.val := rfl

lemma div_cast {x y : BitVec w} : (x / y).val = x.val / y.val := rfl


lemma shiftLeft_cast {x : BitVec w} :
  (x <<< n).val = (x.val <<< n) % 2^w := rfl

lemma shiftRight_cast {x : BitVec w} :
  (x >>> n).val = (x.val >>> n) := rfl

--should we use `shiftr_eq_div_pow` or not?
theorem extract_cast : (extract i j x).val = x.val / 2^j % (2^(i - j + 1)) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_shiftr, shiftr_eq_div_pow]

lemma append_eq_add_val {x: BitVec w} {y : BitVec v} : (x ++ y).val = x.val * 2^v + y.val := by
  simp only [HAppend.hAppend, BitVec.append, BitVec.val_bitvec_eq, append_eq_add y.isLt, mul_comm]

--this was a private lemma but had to use it for rewrite rules
lemma cast_heq {x : BitVec w} (h: w=v) : (h ▸ x).val = x.val := by
  rw [← val_to_ofNat (show x.val < 2^v from (h.symm ▸ x.isLt)), BitVec.val_bitvec_eq]
  exact eq_of_heq (rec_heq_iff_heq.mpr (ofNat_to_val' _ h.symm))

--this should be stated as 2^(i+w)*(bla) + bla instead
lemma signExtend_succ {x: BitVec w} (h: 0 < w) : (signExtend (succ i) x).val =  (signExtend i x).val + 2 ^ (i+w) * Bool.toNat (testBit (x.val) (w - 1)) := by
  simp only [signExtend, cast_heq, append_eq_add_val, repeat_, extract]
  rw [show w - 1 - (w - 1) + 1 = 1 by simp]
  simp [cast_heq, testBit_eq_ofNat, add_mul, mul_assoc, ← pow_add, add_rotate _ _ x.val, mul_comm _ (2^(i+w))]

lemma signExtend_zero {x: BitVec w} (_: 0 < w) : (signExtend 0 x).val = x.val := by
  simp [signExtend, cast_heq, append_eq_add_val, repeat_, extract]

theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = testBit x.val i := by rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w): (BitVec.ofNat w x)[i] = testBit x i := by
  simp [BitVec.ofNat, GetElem.getElem, lsbGet, extract, Fin.ofNat', mod_eq_of_lt, h2]

theorem xor_eq_xor' {m n : Nat} : m ^^^ n = Nat.lxor' m n := by
  simp only [Nat.xor, bitwise_eq_bitwise' bne (by simp), HXor.hXor, Xor.xor, lxor']
  congr; aesop

lemma and_eq_and' : m &&& n = land' m n := by
  simp [HAnd.hAnd, AndOp.and, land, land', bitwise_eq_bitwise']

lemma or_eq_or' : m ||| n = lor' m n := by
  simp [HOr.hOr, OrOp.or, lor, lor', bitwise_eq_bitwise']

theorem extract_val {x : BitVec (w + 1)} (h : j ≤ w) : (BitVec.extract w j x).val = x.val >>> j := by
  simp only [BitVec.ofNat, Fin.ofNat', extract]
  rw [mod_eq_of_lt]
  rw [shiftRight_eq_shiftr, shiftr_eq_div_pow, ← Nat.sub_add_comm h]
  rw [← pow_div (by linarith) (by decide)]
  exact Nat.div_lt_div_of_lt_of_dvd ((Nat.pow_dvd_pow_iff_le_right (by decide)).mpr (by linarith)) x.isLt

lemma shiftRight_zero : m >>> 0 = m := rfl

theorem extract_val' {x : BitVec w} : (BitVec.extract j 0 x).val = x.val % 2^(j + 1) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_zero]

lemma extract_eq_testBit {x : BitVec w} : (x.extract j j).val = (x.val.testBit j).toNat := by
  simp [extract_cast, testBit, BitVec.ofNat, Fin.ofNat', shiftr_eq_div_pow, shiftRight_eq_shiftr, mod_two_of_bodd]

theorem extract_eq_msb {x : BitVec (w + 1)} : (x.extract w w).val = (msb x).toNat := by
  simp only [msb, getMsb, getLsb, extract_eq_testBit, succ_pos] ; congr

lemma toNat_inj {a b : Bool} : a.toNat = b.toNat ↔ a=b := by cases' a <;> cases' b <;> aesop

theorem msb_eq_testBit {x : BitVec (w + 1)} : msb x = x.val.testBit w := by
  apply toNat_inj.mp
  exact Eq.trans (@extract_eq_msb _ x).symm (@extract_eq_testBit _ _ x)

theorem msb_eq_val (c : BitVec 1) : (msb c).toNat = c.val := by
  simp only [msb_eq_testBit]
  have := c.isLt
  interval_cases c.val <;> simp

/-! ### Equivalence between bitwise and BitVec operations -/

theorem BV_add {x y : BitVec w}: bitwise_add x.val y.val w = (x + y).val := by
  rw [bitwise_add_eq_add]
  norm_cast

theorem BV_neg {x : BitVec w}: bitwise_neg x.val w = x.neg.val := by
  simp only [bitwise_neg_eq_neg, x.isLt]
  norm_cast

theorem BV_mul {x y : BitVec w} (h : 0 < w): bitwise_mul x.val y.val w = (x * y).val := by
  rw [bitwise_mul_eq_mul h]
  norm_cast

theorem BV_extract {x : BitVec w} : bitwise_extract x.val i j = (extract i j x).val := by
  rw [bitwise_extract_eq_extract]
  norm_cast

theorem BV_concat {x : BitVec w} {y : BitVec v} : bitwise_concat y.val x.val v w  = (x ++ y).val := by
  rw [bitwise_concat_eq_concat y.isLt x.isLt]
  norm_cast

theorem BV_eq {x y : BitVec w} (h: 0 < w): bitwise_eq x.val y.val w = (x = y) := by
  simp [← bitwise_eq_eq h x.isLt y.isLt]

theorem BV_ult {x y : BitVec w} (h1: x < y) : bitwise_ult x.val y.val w:= bitwise_ult_of_ult y.isLt (val_bitvec_lt.mpr h1)

--TODO
-- theorem BV_slt {x y : BitVec w} (h1: x < y) : bitwise_slt x.val y.val w:= sorry

theorem BV_signExtend {x : BitVec w} (h: 0 < w): (signExtend i x).val = bitwise_ext x.val w i := by
  induction' i with i ih
  · rw [signExtend_zero h, bitwise_ext_zero x.isLt]
  · simp only [bitwise_ext, toNat] at ih ⊢
    rw [toNat_succ, add_eq]
    simp only [add_comm, ← ih, (show ¬ w+i < w by linarith), ite_false]
    simp [signExtend_succ h, add_comm w i, ih]
-- if we use bitvec = bitvec version then make another lemma that reduces it to the .val version above (so that you dont reprove it every single time)
-- swap lhs and rhs

end BitVec
