/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed, Wojciech Nawrocki, Joe Hendrix
-/

import Mathlib
import Std


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

theorem pow_two_pos (w : Nat) : 0 < 2^w := pow_pos (by decide) _ -- do we need this?

protected def zero (w : Nat) : BitVec w :=
  ⟨0, pow_two_pos w⟩

/-- The bitvector `n mod 2^w`. -/
protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (pow_two_pos w)

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

#check Nat.add_div_of_dvd_right
/-- `a ≠ b` as natural numbers if and only if `a != b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_bitvec_bne {a b : BitVec w} : a.val ≠ b.val ↔ a != b := by
  simp [bne]

theorem shiftRight_eq_shiftr: n >>> m = Nat.shiftr n m := sorry

theorem bitwise_lt (hx : x < 2^n) (hy: y< 2^n) (h: f false false = false): Nat.bitwise f x y < 2^n := sorry

lemma concat_size (hx : x < 2^n) (hy: y< 2^m) : y <<< n ||| x < 2^(n+m) := sorry

lemma pow_two_succ (n: Nat) : 2^(n+1) = 2^n +2^n := sorry

protected def complement (x : BitVec w) : BitVec w :=
  0 - (x + .ofNat w 1)

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, by simp [HAnd.hAnd, AndOp.and, Nat.land, bitwise_lt]⟩ -- why do i have to unfold everything?

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, by simp [HOr.hOr, OrOp.or, Nat.lor, bitwise_lt]⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, by simp [HXor.hXor, Xor.xor, Nat.xor, bitwise_lt]⟩

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  .ofNat w (x.val <<< n)

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, by 
      simp only [shiftRight_eq_shiftr, Nat.shiftr_eq_div_pow]
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
  ⟨x.val <<< v ||| y.val, Nat.add_comm _ _ ▸ concat_size y.isLt x.isLt⟩ -- is it swapped? why?

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
  <;> simp [Nat.testBit, BitVec.ofNat, Fin.ofNat', h, Nat.mod_two_of_bodd, Nat.shiftRight, shiftRight_eq_shiftr] --probably some API missing here.. shouldnt have to take cases
  aesop-- non-terminating simp :(
  
lemma toNat_le_one (b: Bool) : b.toNat ≤ 1 := sorry

@[simp] lemma toNat_eq_bif {b: Bool}: cond b 1 0 = b.toNat := sorry --in the other file

instance : GetElem (BitVec w) Nat Bool (fun _ i => i < w) where
  getElem x i _ := Nat.testBit x.val i

@[simp] lemma bit_0 (b : Bool) : Nat.bit b 0 = b.toNat := by
  cases' b <;> simp

@[simp] lemma bit_1 (b : Bool) (n : Nat) : Nat.bit b 1 = 2+b.toNat:= by
  cases' b <;> simp

def Nat.lt_self_sub_one (h : 0 < w) : w - 1 < w := Nat.lt_of_succ_le ((Nat.sub_add_cancel (Nat.succ_le_of_lt h)) ▸ Nat.le.refl) -- should be in mathlib. also should be in the other file.

def bitwise_extract (x i j: Nat) : Nat := go x j 0 (i-j)
where
  go (x j z : Nat) : Nat → Nat
  | 0     => z.bit (x.testBit j)
  | i + 1 => go x j (z.bit (x.testBit (i+1+j))) i

lemma bitwise_extract_size : bitwise_extract x n m < 2^(n-m+1) := sorry

--change formatoof rhs to extract
theorem bitwise_extract_eq_extract : bitwise_extract x.val i j = (extract i j x).val := sorry

theorem bV_extract {x : BitVec w} : BitVec.ofNat (i-j+1) (bitwise_extract x.val i j)= extract i j x := by
  rw [← val_bitvec_eq]
  simp [bitwise_extract_eq_extract, BitVec.ofNat, Fin.ofNat']


def bitwise_concat (x y n m: Nat) : Nat := go x y n 0 (n+m-1)
where
  go (x y n z: Nat) : Nat → Nat
  | 0     => z.bit (x.testBit 0)
  | i + 1 => if i+1 < n then go x y n (z.bit (x.testBit (i+1))) i else go x y n (z.bit (y.testBit (i+1-n))) i

lemma bitwise_concat_size (h: 0< n): bitwise_concat x y n m < 2^(m+n) := sorry

theorem bitwise_concat_eq_concat (hx : x < 2^n) (hy: y< 2^m): bitwise_concat x y n m = y <<< n ||| x := sorry

lemma testBit_concat (h: 0< n) (h2: k ≤ n+m-1): (bitwise_concat x y n m).testBit k = if k < n then x.testBit k else y.testBit (k-n) := sorry

lemma or_eq_or': Nat.bitwise or = lor' := sorry

theorem bV_concat {x : BitVec w} {y : BitVec v} (h: 0 < v): (x ++ y).val = bitwise_concat y.val x.val v w := by
  simp [HAppend.hAppend, BitVec.append, bitwise_concat_eq_concat y.isLt x.isLt]

def bitwise_ext (x n k: Nat) := go x (n-1) 0 (n+k-1)
where
  go (x n z : Nat) : Nat → Nat
  | 0     => z.bit (x.testBit 0)
  | i + 1 => if i+1 < n then go x n (z.bit (x.testBit (i+1))) i else go x n (z.bit (x.testBit n)) i

@[simp] lemma unfold_bitwise_ext : bitwise_ext x n k = bitwise_ext.go x (n-1) 0 (n+k-1) := rfl

lemma testBit_eq_ofNat {x: BitVec w} : Bool.toNat (Nat.testBit (x.val) k) = (BitVec.ofNat 1 (x.val >>> k)).val:= by
  simp only [BitVec.ofNat, Fin.ofNat', Nat.testBit, shiftRight_eq_shiftr, Nat.mod_two_of_bodd, pow_one]
  aesop

lemma lt_succ_pow_two {y b i : Nat} (h: b ≤ 1) (hy : y < 2^i) : 2^i * b + y < 2^(i+1) := sorry


lemma bitwise_ext_succ : bitwise_ext.go x n y m = bitwise_ext.go x n 0 m + 2^(m+1)*y := sorry

lemma val_to_ofNat (h: m < 2^w) : (BitVec.ofNat w m).val = m := by simp [BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt h]

lemma ofNat_to_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt x.isLt]


lemma extract_eq_shiftr : (extract i j x).val =  Nat.shiftr x.val j := by
  simp [extract, ofNat_to_val x, shiftRight_eq_shiftr]
  sorry


lemma ofNat_to_val' (x : BitVec w) (h : v = w): HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_to_val x).symm

theorem append_eq_add (hy: y< 2^m): x <<< m ||| y = 2^m*x + y := sorry

lemma bVappend_eq_add {a: BitVec w} {b : BitVec u} : (a ++ b).val = a.val*2^u+b.val := by
  simp only [HAppend.hAppend, BitVec.append, BitVec.val_bitvec_eq, append_eq_add b.isLt, mul_comm]


private lemma cast_heq {x : BitVec w} (h: w=v) : (h ▸ x).val = x.val := by
  rw [← val_to_ofNat (show x.val < 2^v from (h.symm ▸ x.isLt)), BitVec.val_bitvec_eq]
  exact eq_of_heq (rec_heq_iff_heq.mpr (ofNat_to_val' _ h.symm)) 

lemma append_assoc {x : BitVec a} {y : BitVec b} {z : BitVec c} : ((x ++ y) ++ z).val = (x ++ (y ++ z)).val := by 
  simp only [HAppend.hAppend, BitVec.append, add_comm b c, append_eq_add (concat_size z.isLt y.isLt)]
  simp only [append_eq_add _, y.isLt, x.isLt, z.isLt]
  ring

theorem append_assoc' {x : BitVec a} {y : BitVec b} {z : BitVec c} :
  ((x ++ y) ++ z) = Nat.add_assoc _ _ _ ▸ (x ++ (y ++ z)) := by
  rw [← val_bitvec_eq, cast_heq, append_assoc]


lemma signExtend_succ {x: BitVec w} (h: 0 < w) : (signExtend (Nat.succ i) x).val =  (signExtend i x).val + 2 ^ (i+w) * Bool.toNat (Nat.testBit (x.val) (w - 1)) := by
  simp only [signExtend, cast_heq, bVappend_eq_add, repeat_, extract]
  rw [show w - 1 - (w - 1) + 1 = 1 by simp]
  simp [cast_heq, testBit_eq_ofNat, add_mul, mul_assoc, ← pow_add, add_rotate _ _ x.val, mul_comm _ (2^(i+w))]

lemma signExtend_zero {x: BitVec w} (h: 0 < w) : (signExtend 0 x).val = x.val := by
  simp [signExtend, cast_heq, bVappend_eq_add, repeat_, extract]

lemma bitwise_ext_size (h: 0< n): bitwise_ext x n m < 2^(n+m) := sorry

lemma bitwise_ext_zero (h: 0 < w) (hx: x < 2^w) : bitwise_ext x w 0 = x := sorry

theorem bv_signExtend {x : BitVec w} (h: 0 < w): (signExtend i x).val = bitwise_ext x.val w i := by
  induction' i with i ih 
  · rw [signExtend_zero h, bitwise_ext_zero h x.isLt]
  · rw [unfold_bitwise_ext] at *
    rw [show w+ Nat.succ i -1 = w + i - 1 + 1 by simp [Nat.sub_add_comm, Nat.sub_add_cancel (show 1 ≤ w + i by linarith)]]
    simp only [bitwise_ext.go, bit_0]
    rw [bitwise_ext_succ, @bitwise_ext_succ _ _ (Bool.toNat (Nat.testBit (x.val) (w - 1))) _]
    rw [Nat.sub_add_cancel (show 1 ≤ w+ i by linarith)]
    simp only [← ih, (show ¬ w+i < w-1 by simp_arith), ite_false]
    simp [signExtend_succ h, Nat.sub_add_cancel (show 1 ≤ i+ w by linarith), add_comm w i, ih]
-- if use bitvec = bitvec version then make another lemma that reduces it to the .val version above (so that you dont reprove it every single time)



lemma eq_of_testBit_eq_lt (h0: x < 2^i) (h1: y< 2^i) (h: ∀ (j : Nat), j < i → x.testBit j = y.testBit j): x = y := sorry

lemma testBit_extract (h: k ≤ i-j) : (bitwise_extract x i j).testBit k = x.testBit (k+j) := sorry

theorem extract_append {x : BitVec w} (hjk : j+1 ≤ k) (hij : i ≤ j): (x.extract k i).val = (x.extract k (j + 1) ++ x.extract j i).val := by
  simp only [extract, HAppend.hAppend, BitVec.append, BitVec.ofNat, Fin.ofNat']
  rw [append_eq_add (Nat.mod_lt _ (pow_two_pos _)), add_comm _ (x.val >>> i % 2 ^ (j - i + 1)), eq_comm]
  apply @And.left _ ((x.val >>> i) % 2^(j-i+1)< 2^(j-i+1)) _
  rw [← Nat.div_mod_unique (pow_two_pos (j-i+1))]
  simp only [shiftRight_eq_shiftr, Nat.shiftr_eq_div_pow]
  apply And.intro _ (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by zify [*, (show i ≤ k by linarith)]; linarith)))
  simp only [Nat.div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  · congr 1; zify [*, (show i ≤ k by linarith)]; ring
  · zify [*]; ring

  -- alternative proof. it bothers me that half of this proof is jst simps to get it to the right form. the real meat is the last 8 lines.
  -- simp only [HAppend.hAppend, BitVec.append, BitVec.ofNat, Fin.ofNat', ← bitwise_extract_eq_extract]
  -- have h1: (j-i+1)+(k-(j+1)+1) = k-i+1 := by zify[hjk, hij, (show i ≤ k by linarith)]; ring
  -- apply eq_of_testBit_eq_lt bitwise_extract_size (h1 ▸ concat_size (bitwise_extract_size) (bitwise_extract_size))
  -- intro l hl
  -- rw [testBit_extract (by linarith), ← bitwise_concat_eq_concat (bitwise_extract_size) (bitwise_extract_size)]
  -- rw [testBit_concat (by linarith) (by simp [h1]; linarith)]
  -- by_cases h2: l < j-i+1
  -- · rw [testBit_extract (by linarith)]
  --   simp [h2]
  -- · have h3: l - (j - i + 1) ≤  k - (j + 1) := by 
  --     push_neg at h2; zify[*] at *; linarith
  --   rw [testBit_extract h3]
  --   have : l-(j-i+1)+(j+1) = l+i := by push_neg at h2; zify [h2, hij]; linarith
  --   simp [h2, this]

theorem bv_extract_whole {x : BitVec w} {h : w ≤ n + 1} : (x.extract n 0).val = x.val := by
  rw [← val_to_ofNat (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_of_le_right (by decide) h)), extract]
  simp [shiftRight_eq_shiftr, Nat.shiftr_eq_div_pow]


theorem bv_extract_extract {x : BitVec w} {hl : k ≤ l} {hk : l ≤ j - i}: ((x.extract j i).extract l k).val = (x.extract (i + l) (i + k)).val := by
  simp only [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_shiftr]
  simp only [Nat.shiftr_eq_div_pow, Nat.div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]
  rw [Nat.mod_mod_of_dvd _ (by apply pow_dvd_pow; zify [*]; linarith)]
  congr 3; zify [hl, hk, add_le_add_left hl]; ring

-- def conditions_ult (x y : BitVec w) (h : w > 0) :=
--   conds x y (w - 1) (Nat.lt_self_sub_one h)
-- where
--   conds (x y : BitVec w) (i : Nat) (h : i < w) : Prop := match i with
--     | 0     => ¬ x[0] ∧ y[0]
--     | i + 1 =>
--       have h : i < w := Nat.lt_of_succ_lt h
--       (¬ x[i + 1] ∧ y[i + 1]) ∨ (¬ (x[i + 1] ∧ ¬y[i + 1]) ∧ conds x y i h)


-- theorem contra_le_of_testBit {n m :ℕ} (i :ℕ) (h: n ≤ m) :  Nat.testBit n i = true ∧ Nat.testBit m i = false → (∃ (j : ℕ), i < j ∧  Nat.testBit n j ≠ Nat.testBit m j) :=by
--   have H := @Nat.lt_of_testBit m n i
--   contrapose! H
--   aesop

-- theorem most_sig_eq_base {m :ℕ} (h : m ≠ 0) : ∃ i, Nat.testBit 0 i ≠ Nat.testBit m i ∧ ∀ j > i, Nat.testBit m j = Nat.testBit 0 j := by
--   have ⟨k, Hk⟩ := Nat.exists_most_significant_bit h
--   use k
--   simp_all
  

-- theorem most_sig_eq {n m :ℕ} (h : n ≠ m) : ∃ i, Nat.testBit n i ≠ Nat.testBit m i ∧ ∀ j > i, Nat.testBit m j = Nat.testBit n j := by
--   by_cases hnz : n = 0
--   · by_cases hmz : m ≠ 0
--     · rewrite [hnz]; exact most_sig_eq_base hmz
--     · push_neg at hmz; rewrite [hnz, hmz] at h; contradiction
--   by_cases hmz : m = 0
--   · rewrite [hmz]
--     have ⟨i, h, h'⟩ := most_sig_eq_base hnz
--     exact ⟨i, Ne.symm h, fun j hj => Eq.symm (h' j hj)⟩ 
--   have H2 : ¬(∀ (i : ℕ), Nat.testBit n i = Nat.testBit m i) := (fun hnq hp => hnq (Nat.eq_of_testBit_eq hp)) h
--   push_neg at H2
--   by_contra' H3
--   replace H3 : ∀ i, Nat.testBit n i ≠ Nat.testBit m i → ∃ j, j>i ∧ Nat.testBit n j ≠ Nat.testBit m j := fun i h => by by_contra' h'; apply H3 ⟨i, ⟨h, fun j hj => Eq.symm (h' j hj)⟩⟩
--   have ⟨k1, Hk1⟩:= Nat.exists_most_significant_bit hnz
--   have ⟨k2, Hk2⟩:= Nat.exists_most_significant_bit hmz
--   have ⟨u, hu⟩ := H2 
--   let M := max k1 k2
--   have H4 : ∀ i:ℕ, ∃ l, l>i ∧ Nat.testBit n l ≠ Nat.testBit m l := by
--     intro i
--     induction' i with d hd
--     · have ⟨v, hv1, hv2⟩ := H3 u hu
--       use v
--       exact ⟨pos_of_gt hv1, hv2⟩ 
--     · have ⟨l, hl1, hl2⟩ := hd
--       have ⟨v, hv1, hv2⟩ := H3 l hl2
--       use v
--       exact ⟨ instTransGtToLTGeToLE.proof_1 hv1 hl1, hv2⟩ 
--   have ⟨l, hl1, hl2⟩ := H4 M
--   replace Hk1 := Hk1.right l (show k1 < l by aesop)
--   replace Hk2 := Hk2.right l (show k2 < l by aesop)
--   rw [← Hk1] at Hk2
--   exact hl2 (Eq.symm Hk2)

-- def lt_of_testBit' {n m :ℕ} (_: n<m) (i :ℕ) : Prop := Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ (∀ (j : ℕ), i < j →  Nat.testBit n j = Nat.testBit m j)

-- theorem lt_of_testBit {n m :ℕ} (h: n < m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ (∀ (j : ℕ), i < j →  Nat.testBit n j = Nat.testBit m j) := by
--   have H := @contra_le_of_testBit n m
--   have ⟨i, hi1, hi2⟩ := most_sig_eq (Nat.ne_of_lt h)
--   by_cases hni : Nat.testBit n i <;> by_cases hmi : Nat.testBit m i
--   · simp [*] at *
--   · replace hmi: Nat.testBit m i = false := by aesop
--     have ⟨j,  hj1, hj2⟩ := H i (Nat.le_of_lt h)  ⟨hni, hmi⟩
--     exfalso
--     have hi3 := Eq.symm (hi2 j (hj1))
--     contradiction
--   · use i
--     exact ⟨ (show _ by simp [hni]), hmi, (show _ by aesop)⟩ 
--   · simp [*] at *


theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = Nat.testBit x.val i := by rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w): (BitVec.ofNat w x)[i] = Nat.testBit x i := by 
  simp [BitVec.ofNat, GetElem.getElem, lsbGet, extract, Fin.ofNat', Nat.mod_eq_of_lt, h2]

/-THERE'S A MUCH QUICKER PROOF using lt_testBit_pow_two_false-/
-- theorem exists_most_significant_bit' {n : BitVec w} : 
--     ∀ i, Nat.testBit n.val i = true → i < w := by
--     have ⟨n, hn⟩ := n
--     intro i h
--     replace h : Nat.testBit n i = true := h
--     by_contra' h2
--     replace h2 : w ≤ i := Nat.le_of_not_lt h2
--     have ⟨k, hk, hj⟩ := Nat.exists_most_significant_bit (show n ≠ 0 by aesop) 
--     have h3: i ≤ k:= by
--       by_contra' h4
--       have h5 := hj i h4
--       simp [h] at h5
--     have h8 := Nat.le_trans h2 h3
--     have ⟨l, hl1, hl2, hl3⟩  := lt_of_testBit hn
--     cases' Nat.eq_or_lt_of_le h8 with h9 h10
--     · by_cases heq : l = w
--       · simp [*] at *
--       · simp_rw [Nat.testBit_two_pow_of_ne (Ne.symm heq)] at hl2
--     · have h7 := Nat.testBit_two_pow w k
--       have h8 : Nat.testBit (2 ^ w) k = false := by
--         apply Bool.bool_eq_false
--         replace h10: w ≠ k := Nat.ne_of_lt h10
--         rw [h7]
--         exact h10
--       have h9 : ∀ j, k < j → Nat.testBit (2^w) j = Nat.testBit n j := by
--         intros j h11
--         rw [hj j h11]
--         have h12 : w < j := Nat.lt_trans h10 h11
--         have h13 := Nat.testBit_two_pow w j
--         apply Bool.bool_eq_false
--         replace h14: w ≠ j := Nat.ne_of_lt h12
--         rw [h13]
--         exact h14
--       exact Nat.lt_asymm hn (Nat.lt_of_testBit k h8 hk h9)


-- theorem Nat.le_of_lt_dec (h : 0 < w) (h' : i < w) : i ≤ w - 1 := le_tsub_of_add_le_right h'

def bitwise_ult (x y w : Nat) := go x y (w - 1) 
where
  go (x y : Nat) : Nat →  Prop
    | 0     => ¬ x.testBit 0  ∧ y.testBit 0
    | i + 1 => (¬ x.testBit (i + 1) ∧ y.testBit (i+1)) ∨ (¬(x.testBit (i + 1) ∧ ¬ y.testBit (i + 1)) ∧ go x y i)

theorem bitwise_ult_of_ult (hy: y< 2^w) (h1: x < y) : bitwise_ult x y w := sorry


theorem ult {x y : BitVec w} (h1: x < y) : bitwise_ult x.val y.val w:= bitwise_ult_of_ult y.isLt (val_bitvec_lt.mpr h1)


-- theorem Nat_to_BitVec (f: BitVec w → Bitvec w →  Prop) (g: Nat → Nat → Prop) (h: f x y = g x.val y.val) : false:= sorry

-- theorem t {x y : BitVec w} {h : 0 < w} (h1 : x.val < y.val): conditions_ult x y h := by 
--   have ⟨i, hi⟩ := lt_of_testBit h1
--   apply bitblast_ult_base' (j := w - 1) (Nat.lt_self_sub_one h) (Nat.le_of_lt_dec h (exists_most_significant_bit' i hi.right.left)) hi
-- where
--  bitblast_ult_base' {i j} (h2 : j < w) (h3 : i ≤ j) : lt_of_testBit' h1 i → conditions_ult.conds x y j h2 := by
--   intro h4
--   unfold lt_of_testBit' at h4
--   have ⟨h41, h42, h43 ⟩ := h4
--   induction' j with j hj
--   · unfold conditions_ult.conds
--     replace h3 := Nat.eq_zero_of_le_zero h3
--     rw [h3] at h41
--     rw [h3] at h42
--     simp [h41, h42, testBit_eq_rep]
--   · unfold conditions_ult.conds
--     cases' (LE.le.eq_or_lt h3) with h5 h6
--     { left
--       rw [h5] at h41
--       rw [h5] at h42
--       simp [h41, h42, testBit_eq_rep]}
--     { replace h6:= SuccOrder.le_of_lt_succ h6 
--       right
--       push_neg
--       exact {left := by intro h7
--                         rw [← h7]
--                         simp [h43 (j+1) (Nat.lt_succ_of_le h6), testBit_eq_rep], 
--               right := hj (Nat.lt_of_succ_lt h2) h6 }}

def toNat (bs : List Bool) : Nat := List.foldr Nat.bit 0 bs

#eval toNat [true, false, false, true]

-- def toNat (bs : List Bool) : Nat :=
--   toNat' (bs.length - 1) bs.reverse
-- where
--   toNat' (e : Nat) : List Bool → Nat
--     | [] => 0
--     | b :: xs  => 2 ^ e*b.toNat + toNat' (e - 1) xs

lemma toNat_lt : toNat bs < 2^bs.length := by
  simp only [toNat]
  induction' bs with b l ih
  · simp
  · simp only [List.foldr, Nat.bit_val, List.length_cons]
    cases' b <;> simp [pow_two_succ, two_mul (List.foldr Nat.bit 0 l)] at * <;> linarith [ih] -- non-terminal simp:(
    -- calc _ ≤ 2*(2^l.length - 1) + 1 := add_le_add (by simp [Nat.le_pred_of_lt ih]) (toNat_eq_bif ▸ toNat_le_one b)
    --      _ = 2 ^ (Nat.succ l.length) -1 := by rw [mul_tsub, pow_succ, ← tsub_tsub_assoc (by decide) (by linarith)]
    --      _ < _ := Nat.pred_lt (ne_of_gt (pow_two_pos (Nat.succ l.length)))
#check List.Subset

def bbT (bs : List Bool): BitVec bs.length :=
  ⟨toNat bs, toNat_lt⟩

-- @[simp] def toNat' (bs : List Bool) : {x : Nat // x < 2 ^ w} :=
--   go w (bs.takeD w false).reverse
--     ((bs.takeD w false).length_reverse ▸ (bs.takeD_length w false).symm)
-- where
--   go (e : Nat) (bs : List Bool) (h : e = bs.length) : {x : Nat // x < 2 ^ e} :=
--     match e, bs with
--     | 0, [] => ⟨0, by decide⟩
--     | e + 1, false :: bs =>
--       let ⟨x, hx⟩ := go e bs (Nat.succ.inj h)
--       ⟨x, Nat.lt_trans hx (Nat.pow_lt_pow_succ (by decide) _)⟩
--     | e + 1, true :: bs  =>
--       let ⟨x, hx⟩ := go e bs (Nat.succ.inj h)
--       ⟨2 ^ e + x, pow_two_succ e ▸ Nat.add_lt_add_left hx _⟩

-- def bbT' (bs : List Bool) : BitVec w :=
--   ⟨(toNat' bs).1, (toNat' bs).2⟩


-- infix:30 " ^^ " => xor

-- variable {x y : BitVec w}

-- def carry (i : Nat) {h : i < w} : Bool := match i with
--   | 0     => false
--   | i + 1 =>
--     have h : i < w := Nat.lt_of_succ_lt h
--     (x[i] && y[i]) || ((x[i] ^^ y[i]) && @carry i h)

-- def go (i : Nat) {h : i < w} : List Bool := match i with
--   | 0     => [(x[0] ^^ y[0]) ^^ @carry w x y 0 h]
--   | i + 1 =>
--     have : i < w := Nat.lt_of_succ_lt h
--     ((x[i + 1] ^^ y[i + 1]) ^^ @carry w x y (i + 1) h) :: @go i this

-- def go_length (hi0: 0 < i) (hiw : i - 1 < w) : i = (@go w x y (i - 1) hiw).length := by
--     induction' i, hi0 using Nat.le_induction with i hi0 ih
--     · simp [go]
--     · have h' : i + 1 - 1 = i - 1 + 1 := Nat.eq_add_of_sub_eq hi0 rfl
--       simp only [h']
--       simp [go]
--       exact ih (by linarith)

-- end bit_add

-- open bit_add in
-- def bit_add (x y : BitVec w) {h : w > 0} : BitVec w :=
--   bbT' (@go w x y (w - 1) (Nat.lt_self_sub_one h))

-- theorem Fin.beq_of_val_eq {n} {i j : Fin n} (h : i.val = j.val) : i == j := by
--   replace h := Fin.eq_of_val_eq h
--   rewrite [h]
--   simp

-- theorem Fin.bne_of_val_ne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : i != j := by
--   replace h := Fin.ne_of_val_ne h
--   simp [bne]
--   apply h
  
-- theorem Fin.ne_of_val_bne {n} {i j : Fin n} (h : i != j) : i.val ≠ j.val := by
--   sorry

-- theorem add_bitblast {x y : BitVec w} {h: w > 0} : x + y = bit_add x y (h := h) := by
--   suffices goal: (x.val + y.val)%(2^w) = (bit_add x y (h := h)).val 
--   sorry
--   sorry

-- def toBool' (x : BitVec w) (h : w > 0) :=
--   (go (w - 1) (Nat.lt_self_sub_one h)).reverse
-- where
--   go (i : Nat) (h: i < w) : List Bool := match i with
--     | 0 => [x[0]]
--     | i + 1 =>
--       have h : i < w := Nat.lt_of_succ_lt h
--       x[i+1] :: go i h
 
-- could just use List.map here
-- def toBool (x w: Nat) :=
--   (go (w - 1)).reverse
-- where
--   go (i : Nat) : List Bool := match i with
--     | 0 => [Nat.testBit x 0]
--     | i + 1 =>
--       Nat.testBit x (i+1) :: go i

def toBool (x w: Nat) := List.map (Nat.testBit x) (List.range w)
#eval toNat (toBool 23 2)

lemma div_add_mod_pow_two (m n : Nat) : n = 2^m*Nat.shiftr n m + n%(2^m):= sorry

theorem mod_pow_two_succ (x i : Nat) : x % 2 ^ (i + 1) = 2^i * (Nat.testBit x i).toNat + x % (2^i):= sorry

lemma eq_zero_or_one_le (n : Nat) : n= 0 ∨ 1 ≤ n := by exact Nat.eq_zero_or_pos n -- do we even need this?

--we probably dont need this. toNat_equiv_testBit proves everything and is more easily applicable everywhere
-- theorem toNat_toBool (x w: Nat) : x%(2^(w+1)) = toNat.toNat' w (toBool.go x w) := by
--   induction' w with w ih
--   · simp [toBool.go, toNat.toNat', Nat.mod_two_of_bodd, Nat.testBit, Nat.shiftr]
--   · rw [mod_pow_two_succ, ih]
--     simp [toNat.toNat', add_comm]

-- lemma list_rec_length {α : Type} {w: Nat} (f: Nat → List α)  (g: Nat → α)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : (f w).length = w+1 := by
--   induction' w with w ih
--   · simp [h0]
--   · simp [h, ih]

-- lemma toBool_length (x w : Nat) : (toBool.go x w).length = w+1 := list_rec_length (toBool.go x) (Nat.testBit x) (by simp[toBool.go]) (by simp[toBool.go])

-- lemma list_rec_reverse {α : Type} (w: Nat) (f: Nat → List α) (h2 : i < (f w).length) (g: Nat → α)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : (f w)[i] = g ((f w).length - (i+1)) := by
--   induction' w with w iw generalizing i
--   · simp [h0]
--   · simp only [h]
--     cases' i with i 
--     · simp [h, list_rec_length _ _ h0 h]
--     · rw [List.cons_getElem_succ, iw (show i < List.length (f w) by simp [Nat.succ_eq_add_one, list_rec_length _ _ h0 h, lt_of_add_lt_add_right] at *; simp [h2])]
--       simp [list_rec_length]

-- lemma toBool_testBit {x i w : Nat} (h: i<(toBool.go x w).length) : (toBool.go x w)[i]= Nat.testBit x ((toBool.go x w).length-(i+1))  := list_rec_reverse w (toBool.go x) h (Nat.testBit x) (by simp[toBool.go]) (by simp[toBool.go])

#check Nat.mul_div_assoc

theorem testBit_translate {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w* b + x) i := sorry

theorem testBit_translate' {x w :Nat} {b:Bool} (h: x<2^w) : Nat.testBit (2^w*b.toNat + x) w = b:= sorry

-- theorem toBool_toNat {l : List Bool} (h: 0<l.length):  toBool.go (toNat.toNat' (l.length -1) l) (l.length -1) = l := by
--   induction' l with b l' ih
--   · simp at h
--   · simp only [toBool.go, toNat.toNat']
--     apply List.ext_get (by simp [toBool_length])
--     cases' eq_zero_or_one_le (List.length l') with hl hl
--     <;> intros n h1 h2
--     <;> rw [← List.getElem_eq_get, ← List.getElem_eq_get, toBool_testBit, Nat.add_comm]
--     · cases' b
--       <;> simp [toBool_length, *, List.length_eq_zero] at *
--       <;> rw [← List.getElem_eq_get]
--       <;> simp [hl, toNat.toNat', toBool_testBit]
--     · cases' eq_zero_or_one_le n with h3 h3
--       · simp [h3, toBool_length]
--         apply testBit_eq_scale_pow_two_bit
--         nth_rewrite 2 [← Nat.sub_add_cancel hl]
--         have := @toNat_lt (l'.reverse)
--         simp only [toNat, List.length_reverse, List.reverse_reverse] at this
--         simp [tsub_add_cancel_of_le hl, this]
--       · rw [toBool_length, ← testBit_eq_scale_pow_two (by simp[toBool_length, tsub_lt_self (Nat.lt_of_succ_le hl) h3])]
--         rw [List.length_cons] at h2
--         rw [(show List.length (b :: l') - 1 - 1 = List.length l' - 1 by simp)]
--         rw [Nat.succ_eq_add_one, Nat.add_comm] at h2
--         simp only [toBool.go] at ih
--         have h4: n-1 < List.length l' := by simp [tsub_add_cancel_of_le hl, Nat.sub_lt_left_of_lt_add h3 h2]
--         have iH: (toBool.go (toNat.toNat' (List.length l' - 1) l') (List.length l' - 1))[n-1]'(by simp[toBool_length, tsub_add_cancel_of_le, hl, h4])= l'[n-1]'(h4) := by
--           simp [ih hl]
--         rw [toBool_testBit, toBool_length] at iH
--         rw [show List.length l' - 1 + 1 - (n - 1 + 1) = List.length l' - n by simp[tsub_add_cancel_of_le, Nat.succ_le_of_lt, hl, h3]] at iH
--         rw [show List.length (b :: l') - 1 + 1 - (n + 1) = List.length l' - n by simp]
--         rw [iH]
--         replace h2 : n-1+1 < List.length (b::l') := by 
--           rw [List.length_cons, Nat.succ_eq_add_one] 
--           simp[tsub_add_cancel_of_le, h3, hl]
--           rw [Nat.add_comm]
--           exact h2
--         suffices goal: l'[n-1]'h4 = (b::l')[n-1+1]'h2
--         · simp only [goal, tsub_add_cancel_of_le h3]
--         exact List.cons_getElem_succ b l' (n-1) h2


 
-- theorem toNat_equiv_testBit (l: List Bool) (h: 0<l.length) (h1: i< l.length) : Nat.testBit (toNat.toNat' (l.length - 1) l) i = l[l.length - (i+1)]'(tsub_lt_self h (Nat.succ_pos i)) := by 
--   induction' l with b l ih generalizing i
--   · simp at h
--   · simp only [toNat.toNat']
--     cases' Nat.eq_zero_or_pos l.length with h0 h0
--     · sorry
--     · have h2: i ≤ l.length :=by sorry
--       cases' lt_or_eq_of_le h2 with h3 h3
--       · rw [← testBit_translate (by sorry), (show List.length (b :: l) - 1 - 1 = List.length l - 1 by simp), ih h0 h3]
--         simp only [(show List.length (b :: l) - (i + 1) = List.length l - (i + 1) + 1 by sorry), List.cons_getElem_succ]
--       · rw [(show (b :: l).length - 1 = l.length by simp), ← h3, testBit_translate' (by sorry)]
--         simp [List.length_cons, h3]


#eval toNat  ([false, false, true])
#eval Nat.testBit 4 2

-- theorem inv_bbT_toBool (x : BitVec w) (h : w > 0) : (bbT' (toBool x h)) = x := by
--   induction' w, h using Nat.le_induction with w h hw
--   · simp only [toBool, toBool.go]
--     have h1: x[0] = true ∨ x[0] = false := by 
--       cases' x[0]
--       <;> simp
--     have h2:= x.isLt
--     apply Fin.eq_of_val_eq
--     cases' h1 with ht hf
--     · rw [ht]
--       simp [bbT', toNat', toNat'.go]
--       sorry
--     · sorry
--   · sorry
/-
.val both sides
use 
theorem temp {x : BitVec w} : List.length (toBool x h) = w := by
  sorry

theorem bla (x :  BitVec w) (y : BitVec (List.length (toBool x h))): False := by
  rw [temp] at y
  have : x = y := sorry
  sorry
-/

-- def carry' (i : Nat) {h : i < w} : Bool := match i with
--   | 0     => false
--   | i + 1 =>
--     have h : i < w := Nat.lt_of_succ_lt h
--     (Nat.testBit x.val i && Nat.testBit y.val i) || ((Nat.testBit x.val i ^^ Nat.testBit y.val i) && @carry' i h)

-- def go' (i : Nat) {h : i < w} : List Bool := match i with
--   | 0     => [(Nat.testBit x.val 0 ^^ Nat.testBit y.val 0) ^^ @carry' w x y 0 h]
--   | i + 1 =>
--     have : i < w := Nat.lt_of_succ_lt h
--     ((Nat.testBit x.val (i + 1) ^^ Nat.testBit y.val (i + 1)) ^^ @carry' w x y (i + 1) h) :: @go' i this


-- def go'' (i : Nat) (z : Nat) {h : i < w} : Nat := match i with
--   | 0     => Nat.bit ((Nat.testBit x.val 0 ^^ Nat.testBit y.val 0) ^^ @carry' w x y 0 h) z
--   | i + 1 =>
--     have : i < w := Nat.lt_of_succ_lt h
--     @go'' i (Nat.bit ((Nat.testBit x.val (i + 1) ^^ Nat.testBit y.val (i + 1)) ^^ @carry' w x y (i + 1) h) z) this

-- lemma go'5_length (x y i : Nat) : (go'5 x y i ).length = i+1 := by
--   induction' i with i ih
--   · simp [go'5]
--   · simp [go'5, ih]

-- lemma foo : 2^(i+1) = 2^i + 2^i := by
--   sorry

-- theorem go'5_eq_go''' (x y w: Nat) : toNat.toNat' w (go'5 x y w) = go''' x y 0 w := by
--   induction' w with w ih
--   · simp [go'5, go''', bit_0, toNat.toNat']
--   · simp only [toNat.toNat', go''', (show Nat.succ w - 1 = w by simp)]
--     rw [ih, bit_0, helper_0]


-- def go_length (hi0: 0 < i) (hiw : i - 1 < w) : i = (@go' w x y (i - 1) hiw).length := by
--     induction' i, hi0 using Nat.le_induction with i hi0 ih
--     · simp [go']
--     · have h' : i + 1 - 1 = i - 1 + 1 := Nat.eq_add_of_sub_eq hi0 rfl
--       simp only [h']
--       simp [go']
--       exact ih (by linarith)


-- def bit_add' (x y : BitVec w) {h : w > 0} : Nat:=
--   toNat (@go' w x y (w - 1) (Nat.lt_self_sub_one h))

-- def bit_add'' (x y : BitVec w) {h : w > 0} : Nat :=
--   @go'' w x y (w - 1) 0 (Nat.lt_self_sub_one h)

-- def bit_add''' (x y : BitVec w) : BitVec w :=
--   ⟨go''' x.val y.val 0 (w - 1), sorry⟩


-- lemma xor_mod_2 (a b : Bool) : toNat [a ^^ b] = (toNat [a] + toNat [b])%2 := by
--   cases' a <;> cases' b <;> simp
--   cases' a <;> cases' b <;> simp
  
-- theorem descend_bv_pre (z : BitVec (w +1)) : z.val - 2^w* bool_to_nat (Nat.testBit z.val w) < 2^w:= by
--   cases' z with z hz
--   have h1 : Nat.testBit z w = true ∨ Nat.testBit z w = false := by
--     cases' Nat.testBit z w
--     <;> simp
--   cases' h1 with h1 h1
--   <;> simp only [h1, bool_to_nat, mul_one, mul_zero, Nat.sub_zero]
--   · apply Nat.sub_lt_left_of_lt_add _ (by convert hz 
--                                           simp)
--     by_contra' h3
--     have ⟨i, h4, h5, h6⟩ := lt_of_testBit h3
--     rw  [Nat.testBit_two_pow w i] at h5
--     rw [h5] at h1
--     rw [h1] at h4
--     contradiction
--   · apply Nat.lt_of_testBit w h1 (Nat.testBit_two_pow_self w)
--     have ⟨i, h4, h5, h6⟩ := lt_of_testBit hz
--     intros j hj
--     rw [Nat.testBit_two_pow (w+1) i] at h5
--     rw [← h5] at h4 h6
--     cases' (LE.le.eq_or_gt (show w+1 ≤ j by aesop)) with hj0 hj0
--     · rw [hj0, h4]
--       exact (Nat.testBit_two_pow_of_ne (show w ≠ w+1 by simp)).symm
--     · rw [h6 j]
--       rw [Nat.testBit_two_pow_of_ne (show w ≠ j by aesop)]
--       apply Nat.testBit_two_pow_of_ne (LT.lt.ne hj0)
--       exact hj0

-- theorem eq_bv (h: v < 2^w): (BitVec.ofNat w v).val = v := by
--   simp [BitVec.ofNat]
--   norm_cast
--   exact Nat.mod_eq_of_lt h
  
-- @[simp] theorem descend_bv (z : BitVec (w +1)) : (BitVec.ofNat w (z.val - 2^w* bool_to_nat (Nat.testBit z.val w))).val = z.val - 2^w* bool_to_nat (Nat.testBit z.val w) := by
--   apply eq_bv
--   apply descend_bv_pre z
--   exact x
--   exact y

-- theorem add_bitblast' {h: w > 0} : (x + y).val = bit_add' x y (h := h) := by
--   suffices goal: (x.val + y.val)%(2^w) = (bit_add' x y (h := h))
--   · rw [← goal]
--     simp [BitVec.add]
--     norm_cast
--   · induction' w, h using Nat.le_induction with w h hw
--     · simp only [(show 2^Nat.succ 0 = 2 by simp)]
--       rw [Nat.add_mod]
--       have h1:= Nat.mod_lt x.val (show 0 <2 by simp)
--       have h2 : ∀ a : Nat, a <2 →  a%2 = @toNat ([Nat.testBit a 0]) := by
--         intros a ha
--         cases' (zero_or_one ha) with ha0 ha1
--         · rw [ha0]
--           simp
--         · rw [ha1]
--           simp
--       rw [h2 (x.val) (Fin.is_lt x), h2 y.val (Fin.is_lt y)]
--       rw [← xor_mod_2]
--       simp [bit_add', bbT', go', carry']
--     /-
    
--     -/
--     · sorry
--       -- have H :=  @hw (BitVec.ofNat w (x.val - 2^w* bool_to_nat (Nat.testBit x.val w))) (BitVec.ofNat w (y.val - 2^w* bool_to_nat (Nat.testBit y.val w))) 
--       -- rw [eq_bv] at H
--       -- rw [eq_bv] at H
--       -- simp only [bit_add', go', toNat]


-- @[simp] lemma toNat_eq_Natbit : a.toNat = Nat.bit a 0 := by
--   cases' a <;> decide

-- lemma pow_2_lift (a n : Nat) : a %(2^(n+1)) = a%2^n ∨ a%(2^(n+1)) = 2^n + a%(2^n) := by
--   cases' (lt_or_ge (a%(2^(n+1))) (2^n)) with h1 h1
--   · left
--     have h2:= Nat.dvd_trans (show 2^n ∣ 2^(n+1) by exact Dvd.intro 2 rfl) (@Nat.dvd_sub_mod (2^(n+1)) a)
--     sorry
--   · sorry

-- theorem t67 {x y : Nat} (h : ((x.testBit i ^^ y.testBit i) ^^ carry''' x y i) = false) : (x + y) % 2 ^ (i + 1) = (x + y) % 2 ^ (i + 2) := by
--   sorry 

-- #eval (BitVec.ofNat 5 15) + (BitVec.ofNat 5 14)
-- #eval @bit_add'' 5 (BitVec.ofNat 5 15) (BitVec.ofNat 5 14) (by simp)

-- theorem add_bitblast'' {h: w > 0} : (x + y).val = @bit_add'' w x y h := by
--   suffices goal: (x.val + y.val)%(2^w) = @go'' w x y (w - 1) 0 (Nat.lt_self_sub_one h)
--   · simp only [bit_add'']
--     rw [← goal]
--     simp [BitVec.add]
--     norm_cast
--   induction' w, h using Nat.le_induction with w h hw
--   · simp only [(show 2^Nat.succ 0 = 2 by simp)]
--     rw [Nat.add_mod]
--     have h1:= Nat.mod_lt x.val (show 0 <2 by simp)
--     have h2 : ∀ a : Nat, a <2 →  a%2 = (Nat.testBit a 0).toNat := by
--       intros a ha
--       cases' (zero_or_one ha) with ha0 ha1
--       · rw [ha0]
--         simp
--       · rw [ha1]
--         simp
--     rw [h2 (x.val) (Fin.is_lt x), h2 y.val (Fin.is_lt y)]
--     rw [← xor_mod_2'']
--     simp [bit_add'', go'', carry']
--   · have H1:= @hw (BitVec.ofNat w (x.val - 2^w* (Nat.testBit x.val w).toNat)) (BitVec.ofNat w (y.val - 2^w* (Nat.testBit y.val w).toNat)) 
--     rw [eq_bv] at H1
--     rw [eq_bv] at H1
--     have H2: ∀n :Nat, (n - 2^w* (Nat.testBit n w).toNat) +2^w* (Nat.testBit n w).toNat = n := by sorry
--     rw [← H2 (x.val), ← H2 (y.val)]
--     rw [mid_assoc]
--     rw [Nat.add_mod]
--     cases' pow_2_lift (x.val - 2 ^ w * Bool.toNat (Nat.testBit (x.val) w) + (y.val - 2 ^ w * Bool.toNat (Nat.testBit (y.val) w))) (w) with H3 H3
--     · rw [H3]
--       rw [H1]
--       simp only [bit_add'', (show w+1-1 = w-1 + 1 by sorry), go'']
--       cases' h6: Nat.bit ((Nat.testBit (x.val) (w - 1 + 1) ^^ Nat.testBit (y.val) (w - 1 + 1)) ^^ carry' (w - 1 + 1)) 0 with h1 h2
--       · simp [go'']
--         rw [(show w-1+1 = w by sorry)] at h6
        

--         suffices goal: (Nat.bit (Nat.testBit (x.val) w) 0 + Nat.bit (Nat.testBit (y.val) w) 0)%2 = 0
--         · sorry
--         rw [show Nat.zero =0 by rfl ] at h6
--         nth_rewrite 3 [←h6]
--         sorry        
--       · sorry
--     · sorry

-- theorem go'5_correct (x y i: Nat) : x%(2^(i+1)) + y%(2^(i+1)) = toNat.toNat' i (go'5 x y i) + 2^(i+1)*(carry''' x y (i+1)).toNat := by
--   induction' i with i hi
--   · simp [toNat.toNat', carry''']
--     cases' hx: Nat.bodd x 
--     <;> cases' hy: Nat.bodd y
--     <;> simp [Nat.mod_two_of_bodd, Nat.testBit, hx, hy, Nat.shiftr]
--   · simp only [toNat.toNat']
--     rw [show Nat.succ i - 1 = i by simp]
--     rw [helper_2 x, helper_2 y]
--     suffices goal: (x % 2 ^ (i + 1) + y % 2 ^ (i + 1)) + 2 ^ (i + 1) * Bool.toNat (Nat.testBit x (i + 1))  +  2 ^ (i + 1) * Bool.toNat (Nat.testBit y (i + 1)) = 2 ^ Nat.succ i * Bool.toNat ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1)) +
--       toNat.toNat' i (go'5 x y i) +
--     2 ^ (Nat.succ i + 1) * Bool.toNat (carry''' x y (Nat.succ i + 1))
--     · rw [← goal]
--       ring
--     rw [hi]
--     rw [unfold_carry''' x y (Nat.succ i)]
--     rw [pow_succ 2 (Nat.succ i), two_mul, add_mul]
--     cases' hx : Nat.testBit x (i+1) 
--     <;> cases' hy : Nat.testBit y (i+1) 
--     <;> cases' hc : carry''' x y (i+1) 
--     <;> simp [Nat.add_left_cancel_iff, Nat.succ_eq_add_one, Nat.add_comm]
--     <;> ring

-- theorem bit_add_finally (x y i : Nat): (x+y)%(2^(i+1)) = toNat.toNat' i (go'5 x y i) := by
--   rw [Nat.add_mod, go'5_correct]
--   suffices goal : toNat.toNat' i (go'5 x y i) < 2^(i+1) 
--   · simp [Nat.mod_eq_of_lt, goal]
--   cases' i with i i
--   · cases' h0: Nat.testBit x 0 ^^ (Nat.testBit y 0 ^^ carry''' x y 0)
--     <;> simp [toNat.toNat', h0]
--   · have := @lt_pow_2_length (go'5 x y (Nat.succ i)) (by simp [go'5_length])
--     simp [go'5_length] at this
--     assumption 

-- lemma go'5_testBit (x y : Nat) (h: i <  w+1) : (go'5 x y w)[i]'(by simp[go'5_length]; assumption) = ((Nat.testBit x (w-i) ^^ Nat.testBit y (w-i)) ^^ carry''' x y (w-i)) := by
--   simp only[go'5_length, list_rec_reverse w (go'5 x y) (by simp[go'5_length]; linarith)  (λ i => (Nat.testBit x i ^^ Nat.testBit y i) ^^ carry''' x y i) (by simp[go'5]) (by simp [go'5])]
--   aesop

-- theorem testBit_add {x y i: Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ carry''' x y i):= by
--   set u := max i (max x y) with hu
--   have h : i ≤ u ∧ x ≤ u ∧ y ≤ u := by simp [hu]
--   have h1: (x+y)%2^(u+1) = x+y := by
--     apply Nat.mod_eq_of_lt
--     rw [pow_two_succ u]
--     apply Nat.add_lt_add
--     <;> exact Nat.lt_of_lt_of_le (Nat.lt_two_pow _) (Nat.pow_le_pow_of_le_right (by norm_num) (by simp[h]))
--   nth_rewrite 1 [← h1]
--   rw [bit_add_finally]
--   nth_rewrite 1 [← Nat.add_sub_cancel u 1]
--   rw [← go'5_length x y (u)]
--   rw [@toNat_equiv_testBit i (go'5 x y u) (by simp[go'5_length]) (go'5_length x y u ▸ Nat.lt_of_le_of_lt h.1 (lt_add_one u))]
--   rw [go'5_testBit _ _ (go'5_length x y u ▸ Nat.sub_lt_self (NeZero.pos (i+1)) (go'5_length x y u ▸ add_le_add_right h.1 1))]
--   simp [go'5_length, h] 


-- theorem descend_bv_pre''' (w : Nat) (z : Nat) (hz: z < 2^(w + 1)) : z - 2^w* (Nat.testBit z w).toNat < 2^w:= by
--   have h1 : Nat.testBit z w = true ∨ Nat.testBit z w = false := by
--     cases' Nat.testBit z w
--     <;> simp
--   cases' h1 with h1 h1
--   <;> simp only [h1, Bool.toNat, cond, mul_one, mul_zero, Nat.sub_zero]
--   · apply Nat.sub_lt_left_of_lt_add _ (by convert hz; simp)
--     by_contra' h3
--     have ⟨i, h4, h5, h6⟩ := lt_of_testBit h3
--     rw  [Nat.testBit_two_pow w i] at h5
--     rw [h5] at h1
--     rw [h1] at h4
--     contradiction
--   · apply Nat.lt_of_testBit w h1 (Nat.testBit_two_pow_self w)
--     have ⟨i, h4, h5, h6⟩ := lt_of_testBit hz
--     intros j hj
--     rw [Nat.testBit_two_pow (w+1) i] at h5
--     rw [← h5] at h4 h6
--     cases' (LE.le.eq_or_gt (show w+1 ≤ j by aesop)) with hj0 hj0
--     · rw [hj0, h4]
--       exact (Nat.testBit_two_pow_of_ne (show w ≠ w+1 by simp)).symm
--     · rw [h6 j]
--       rw [Nat.testBit_two_pow_of_ne (show w ≠ j by aesop)]
--       apply Nat.testBit_two_pow_of_ne (LT.lt.ne hj0)
--       exact hj0

-- theorem xor_false : p ^^ false = p := by
--   cases' p
--   <;> simp

-- lemma helper_0 (x y : Nat) : go''' x y 1 i = 2 ^ i + go''' x y 0 i := by sorry

-- theorem helper_1 {x y : Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ carry''' x y i) := by
--   induction' i with i hi
--   · simp [carry''']
--     cases hx : x.testBit 0 <;> cases hy : y.testBit 0
--     <;> unfold Nat.testBit
--     <;> unfold Nat.shiftr
--     <;> rw [Nat.bodd_add]
--     <;> unfold Nat.testBit at hx
--     <;> unfold Nat.shiftr at hx
--     <;> unfold Nat.testBit at hy
--     <;> unfold Nat.shiftr at hy
--     <;> rw [hx, hy]
--   · simp [carry''', Nat.testBit, Nat.shiftr]
--     sorry

-- #check Nat.bit

-- theorem go'''_helper (x y : Nat) : go''' x y 0 i + 2^(i+1)*(carry''' x y (i+1)).toNat= x % 2 ^ (i + 1) + y % 2^(i+1) := by
--   induction' i with i hi
--   · simp [go''']
--     sorry
--   · unfold go'''

--     rw [helper_2 x (i+1), helper_2 y (i+1)]
--     suffices goal: go''' x y (Nat.bit ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1))
--       (Bool.toNat (carry''' x y (Nat.succ i + 1)))) i = (x % 2 ^ (i + 1) + y % 2 ^ (i + 1))+ (2 ^ (i + 1) * Bool.toNat (Nat.testBit x (i + 1))  + 2 ^ (i + 1) * Bool.toNat (Nat.testBit y (i + 1)))
--     · sorry
--     rw [← hi]
--     cases' h : ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1))
--     · rw [h]

--     · sorry

-- theorem bit_add'''_bitblast {h : w > 0} : (x + y).val = (bit_add''' x y).val := by
--   have ⟨x, hx⟩ := x
--   have ⟨y, hy⟩ := y
--   simp only [bit_add''', HAdd.hAdd, Add.add, BitVec.add, Fin.add]
--   rw [go'''_correct x y]
--   sorry
def uDivModRec (a b : Nat) (w : Nat) : (Nat × Nat) :=
  match w with
  | 0    => (0, 0)
  | w + 1 =>
    let (q1, r1) := uDivModRec (a >>> 1) b w --want to use bitwise shift right instead of a >>> 1 same thing below
  
    let (q1, r1) := (q1 <<< 1, r1 <<< 1)
    
    let (r1ShiftAdd, _) := bitwise_add r1 0 w (a.testBit 0)
    let notB := bitwise_negate b w
    let (rMinusB, co1) := bitwise_add r1ShiftAdd notB w true
    let sign := !co1

    -- ...

    let (aMinusB, co2) := bitwise_add a notB w true
    let aLtB := !co2

    



    _

end BitVec
