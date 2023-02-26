/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki
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

theorem Fin.beq_of_val_eq {n} {i j : Fin n} (h : i.val = j.val) : i == j := by
  replace h := Fin.eq_of_val_eq h
  rewrite [h]
  simp

theorem Fin.bne_of_val_ne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : i != j := by
  replace h := Fin.ne_of_val_ne h
  simp [bne]
  apply h
  
theorem Fin.ne_of_val_bne {n} {i j : Fin n} (h : i != j) : i.val ≠ j.val := by
  sorry


def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

namespace BitVec

theorem pow_two_gt_zero (w : Nat) : 2^w > 0 :=
  Nat.pos_pow_of_pos _ (by decide)

protected def zero (w : Nat) : BitVec w :=
  ⟨0, pow_two_gt_zero w⟩

/-- The bitvector `n mod 2^w`. -/
protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (pow_two_gt_zero w)

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

-- We inherit `Fin` implementations when fast but write mod/div
-- ourselves to avoid the extra modulo operation.
protected def add (x y : BitVec w) : BitVec w := Fin.add x y
protected def sub (x y : BitVec w) : BitVec w := Fin.sub x y
protected def mul (x y : BitVec w) : BitVec w := Fin.mul x y

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
@[norm_cast, simp]
theorem val_bitvec_lt {a b : BitVec w} : (a.val : ℕ) < (b.val : ℕ) ↔ a < b := by
  simp [LT.lt, BitVec.lt]


/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_bitvec_bne {a b : BitVec w} : a.val ≠ b.val ↔ a != b := by
  simp [bne]

protected def complement (x : BitVec w) : BitVec w :=
  0 - (x + .ofNat w 1)

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, by simp
                       cases x
                       sorry

                                            
                      ⟩

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, sorry⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, sorry⟩

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  .ofNat w (x.val <<< n)

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, sorry⟩

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
  ⟨x.val <<< v ||| y.val, sorry⟩

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

#eval BitVec.lsbGet (⟨100, sorry⟩ : BitVec 5) 2
#eval Nat.testBit 100 2

theorem lsbGet_equiv_testBit {x : BitVec w} : x.lsbGet i = x.val.testBit i := by
  induction' i with i hi
  · 
    cases h : lsbGet x Nat.zero
    · sorry
    · simp [lsbGet, extract, Nat.testBit, BitVec.ofNat, Fin.ofNat', HShiftRight.hShiftRight, ShiftRight.shiftRight, Nat.shiftRight, Nat.shiftr] at h
      replace h := Fin.ne_of_val_bne h
      replace h : x.val % 2 ≠ 0 := h 
      sorry
  · sorry
  -- simp[lsbGet, extract, BitVec.ofNat, Fin.ofNat', Nat.testBit, HShiftRight.hShiftRight, ShiftRight.shiftRight]





instance : GetElem (BitVec w) Nat Bool (fun _ i => i < w) where
  getElem x i _ := Nat.testBit x.val i





def Nat.lt_self_sub_one (h : 0 < w) : w - 1 < w := Nat.lt_of_succ_le ((Nat.sub_add_cancel (Nat.succ_le_of_lt h)) ▸ Nat.le.refl)

def conditions_ult (x y : BitVec w) (h : w > 0) :=
  conds x y (w - 1) (Nat.lt_self_sub_one h)
where
  conds (x y : BitVec w) (i : Nat) (h : i < w) : Prop := match i with
    | 0     => ¬ x[0] ∧ y[0]
    | i + 1 =>
      have h : i < w := Nat.lt_of_succ_lt h
      (¬ x[i + 1] ∧ y[i + 1]) ∨ (¬ (x[i + 1] ∧ ¬y[i + 1]) ∧ conds x y i h)


theorem contra_le_of_testBit {n m :ℕ} (i :ℕ) (h: n ≤ m) :  Nat.testBit n i = true ∧ Nat.testBit m i = false → (∃ (j : ℕ), i < j ∧  Nat.testBit n j ≠ Nat.testBit m j) :=by
  have H := @Nat.lt_of_testBit m n i
  contrapose! H
  aesop

theorem most_sig_eq_base {m :ℕ} (h : m ≠ 0) : ∃ i, Nat.testBit 0 i ≠ Nat.testBit m i ∧ ∀ j > i, Nat.testBit m j = Nat.testBit 0 j := by
  have ⟨k, Hk⟩ := Nat.exists_most_significant_bit h
  use k
  simp_all
  

theorem most_sig_eq {n m :ℕ} (h : n ≠ m) : ∃ i, Nat.testBit n i ≠ Nat.testBit m i ∧ ∀ j > i, Nat.testBit m j = Nat.testBit n j := by
  by_cases hnz : n = 0
  · by_cases hmz : m ≠ 0
    · rewrite [hnz]; exact most_sig_eq_base hmz
    · push_neg at hmz; rewrite [hnz, hmz] at h; contradiction
  by_cases hmz : m = 0
  · rewrite [hmz]
    have ⟨i, h, h'⟩ := most_sig_eq_base hnz
    exact ⟨i, Ne.symm h, fun j hj => Eq.symm (h' j hj)⟩ 
  have H2 : ¬(∀ (i : ℕ), Nat.testBit n i = Nat.testBit m i) := (fun hnq hp => hnq (Nat.eq_of_testBit_eq hp)) h
  push_neg at H2
  by_contra' H3
  replace H3 : ∀ i, Nat.testBit n i ≠ Nat.testBit m i → ∃ j, j>i ∧ Nat.testBit n j ≠ Nat.testBit m j := fun i h => by by_contra' h'; apply H3 ⟨i, ⟨h, fun j hj => Eq.symm (h' j hj)⟩⟩
  have ⟨k1, Hk1⟩:= Nat.exists_most_significant_bit hnz
  have ⟨k2, Hk2⟩:= Nat.exists_most_significant_bit hmz
  have ⟨u, hu⟩ := H2 
  let M := max k1 k2
  have H4 : ∀ i:ℕ, ∃ l, l>i ∧ Nat.testBit n l ≠ Nat.testBit m l := by
    intro i
    induction' i with d hd
    · have ⟨v, hv1, hv2⟩ := H3 u hu
      use v
      exact ⟨pos_of_gt hv1, hv2⟩ 
    · have ⟨l, hl1, hl2⟩ := hd
      have ⟨v, hv1, hv2⟩ := H3 l hl2
      use v
      exact ⟨ instTransGtToLTGeToLE.proof_1 hv1 hl1, hv2⟩ 
  have ⟨l, hl1, hl2⟩ := H4 M
  replace Hk1 := Hk1.right l (show k1 < l by aesop)
  replace Hk2 := Hk2.right l (show k2 < l by aesop)
  rw [← Hk1] at Hk2
  exact hl2 (Eq.symm Hk2)

def lt_of_testBit' {n m :ℕ} (_: n<m) (i :ℕ) : Prop := Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ (∀ (j : ℕ), i < j →  Nat.testBit n j = Nat.testBit m j)

theorem lt_of_testBit {n m :ℕ} (h: n < m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ (∀ (j : ℕ), i < j →  Nat.testBit n j = Nat.testBit m j) := by
  have H := @contra_le_of_testBit n m
  have ⟨i, hi1, hi2⟩ := most_sig_eq (Nat.ne_of_lt h)
  by_cases hni : Nat.testBit n i <;> by_cases hmi : Nat.testBit m i
  · simp [*] at *
  · replace hmi: Nat.testBit m i = false := by aesop
    have ⟨j,  hj1, hj2⟩ := H i (Nat.le_of_lt h)  ⟨hni, hmi⟩
    exfalso
    have hi3 := Eq.symm (hi2 j (hj1))
    contradiction
  · use i
    exact ⟨ (show _ by simp [hni]), hmi, (show _ by aesop)⟩ 
  · simp [*] at *


theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = Nat.testBit x.val i := by rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w): (BitVec.ofNat w x)[i] = Nat.testBit x i := by 
unfold BitVec.ofNat
simp [GetElem.getElem, lsbGet, extract]
rw [Nat.mod_eq_of_lt h2]


theorem exists_most_significant_bit' {n : BitVec w} :
    ∀ i, Nat.testBit n.val i = true → i < w := by
    have ⟨n, hn⟩ := n
    intro i h
    replace h : Nat.testBit n i = true := h
    by_contra' h2
    replace h2 : w ≤ i := Nat.le_of_not_lt h2
    have ⟨k, hk, hj⟩ := Nat.exists_most_significant_bit (show n ≠ 0 by aesop) 
    have h3: i ≤ k:= by
      by_contra' h4
      have h5 := hj i h4
      rw [h] at h5
      contradiction
    have h8 := Nat.le_trans h2 h3
    have ⟨l, hl1, hl2, hl3⟩  := lt_of_testBit hn
    cases' Nat.eq_or_lt_of_le h8 with h9 h10
    · by_cases heq : l = w
      · rw [h9] at heq
        rw [heq] at hl1
        rw [hk] at hl1
        contradiction
      · have h11 := Nat.testBit_two_pow_of_ne (Ne.symm heq)
        rw [h11] at hl2
        contradiction
    · have h7 := Nat.testBit_two_pow w k
      have h8 : Nat.testBit (2 ^ w) k = false := by
        apply Bool.bool_eq_false
        replace h10: w ≠ k := Nat.ne_of_lt h10
        rw [h7]
        exact h10
      have h9 : ∀ j, k < j → Nat.testBit (2^w) j = Nat.testBit n j := by
        intros j h11
        rw [hj j h11]
        have h12 : w < j := Nat.lt_trans h10 h11
        have h13 := Nat.testBit_two_pow w j
        apply Bool.bool_eq_false
        replace h14: w ≠ j := Nat.ne_of_lt h12
        rw [h13]
        exact h14
      have H := Nat.lt_of_testBit k h8 hk h9
      exact Nat.lt_asymm hn H


theorem Nat.le_of_lt_dec (h : 0 < w) (h' : i < w) : i ≤ w - 1 := le_tsub_of_add_le_right h'

theorem t {x y : BitVec w} {h : 0 < w} (h1 : x.val < y.val): conditions_ult x y h := by 
  have ⟨i, hi⟩ := lt_of_testBit h1
  apply bitblast_ult_base' (j := w - 1) (Nat.lt_self_sub_one h) (Nat.le_of_lt_dec h (exists_most_significant_bit' i hi.right.left)) hi
where
 bitblast_ult_base' {i j} (h2 : j < w) (h3 : i ≤ j) : lt_of_testBit' h1 i → conditions_ult.conds x y j h2 := by
  intro h4
  unfold lt_of_testBit' at h4
  have ⟨h41, h42, h43 ⟩ := h4
  induction' j with j hj
  · unfold conditions_ult.conds
    replace h3 := Nat.eq_zero_of_le_zero h3
    rw [h3] at h41
    rw [h3] at h42
    simp [h41, h42, testBit_eq_rep]
  · unfold conditions_ult.conds
    cases' (LE.le.eq_or_lt h3) with h5 h6
    { left
      rw [h5] at h41
      rw [h5] at h42
      simp [h41, h42, testBit_eq_rep]}
    { replace h6:= SuccOrder.le_of_lt_succ h6 
      right
      push_neg
      exact {left := by intro h7
                        rw [← h7]
                        simp [h43 (j+1) (Nat.lt_succ_of_le h6), testBit_eq_rep], 
              right := hj (Nat.lt_of_succ_lt h2) h6 }}

def toNat (bs : List Bool) : Nat :=
  toNat' (bs.length - 1) bs.reverse
where
  toNat' (e : Nat) : List Bool → Nat
    | [] => 0
    | false :: xs => toNat' (e - 1) xs
    | true :: xs  => 2 ^ e + toNat' (e - 1) xs

@[simp] def bbT (bs : List Bool): BitVec bs.length :=
  ⟨toNat bs, by
  unfold toNat
  rewrite [← List.length_reverse]
  induction bs.reverse with 
  | nil => simp
  | cons b l ih => cases b with
    | false =>
      simp [Nat.pow_succ]
      apply Nat.lt_of_le_of_lt _ (Nat.mul_lt_mul_of_pos_right ih (show 2>0 by simp))
      have u: toNat.toNat' (List.length l) (false :: l) = toNat.toNat' _ l := rfl
      rw [u]
      rw [← Nat.mul_one (toNat.toNat' _ l), Nat.mul_assoc]
      apply Nat.mul_le_mul_left (toNat.toNat' _ l)
      simp
    | true =>
      simp [Nat.pow_succ]
      have u : toNat.toNat' _ (true :: l) = 2^(List.length l) + toNat.toNat' _ l := rfl
      have : 2^(List.length l)*2 = 2^(List.length l)+ 2^(List.length l) := by simp [Nat.mul_add, show 2 = 1+1 from rfl]
      rw [u, this]
      simp [ih, Nat.add_lt_add_left _ (2^(List.length l))]
  ⟩

infix:30 " ^^ " => xor

namespace bit_add

variable {x y : BitVec w}

def carry (i : Nat) {h : i < w} : Bool := match i with
  | 0     => false
  | i + 1 =>
    have h : i < w := Nat.lt_of_succ_lt h
    (x[i] && y[i]) || ((x[i] ^^ y[i]) && @carry i h)

def go (i : Nat) {h : i < w} : List Bool := match i with
  | 0     => [(x[0] ^^ y[0]) ^^ @carry w x y 0 h]
  | i + 1 =>
    have : i < w := Nat.lt_of_succ_lt h
    ((x[i + 1] ^^ y[i + 1]) ^^ @carry w x y (i + 1) h) :: @go i this

def go_length (hi0: 0 < i) (hiw : i - 1 < w) : i = (@go w x y (i - 1) hiw).length := by
    induction' i, hi0 using Nat.le_induction with i hi0 ih
    · simp [go]
    · have h' : i + 1 - 1 = i - 1 + 1 := Nat.eq_add_of_sub_eq hi0 rfl
      simp only [h']
      simp [go]
      exact ih (by linarith)

end bit_add

open bit_add in
def bit_add (x y : BitVec w) {h : w > 0} : BitVec w :=
  go_length h (Nat.lt_self_sub_one h) ▸ bbT (@go w x y (w - 1) _)

theorem add_bitblast {x y : BitVec w} {h: w > 0} : x + y = bit_add x y (h := h) := sorry




def toBool (x : BitVec w) (h : w > 0) :=
  (go (w - 1) (Nat.lt_self_sub_one h)).reverse
where
  go (i : Nat) (h: i < w) : List Bool := match i with
    | 0 => [x[0]]
    | i + 1 =>
      have h : i < w := Nat.lt_of_succ_lt h
      x[i+1] :: go i h
 
theorem temp {x : BitVec w} : List.length (toBool x h) = w := by
  sorry

#eval bbT (toBool (BitVec.ofNat 8 259) (by decide))

theorem inv_bbT_toBool (x : BitVec w) (h : w > 0) : (bbT (toBool x h)).val = x.val := by
  sorry

theorem bla (x :  BitVec w)  (h : w > 0) : False := by
  set y : BitVec _ := (bbT (toBool x h)) with hy
  have h' : y.val = x.val := by simp [hy]; apply inv_bbT_toBool
  rw [temp] at y
  have : x = y := sorry
  sorry

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
end BitVec
