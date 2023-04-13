/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Harun Khan
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

lemma zero_or_one {n: Nat} (h: n < 2) : n = 0 ∨ n = 1 := by
  induction' n with n ih
  · simp
  · induction' n with m
    · simp
    · linarith


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
sorry


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
      exact Nat.lt_asymm hn (Nat.lt_of_testBit k h8 hk h9)


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

@[simp] def toNat (bs : List Bool) : Nat :=
  toNat' (bs.length - 1) bs.reverse
where
  toNat' (e : Nat) : List Bool → Nat
    | [] => 0
    | b :: xs  => 2 ^ e*b.toNat + toNat' (e - 1) xs

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
      have u: toNat.toNat' (List.length l) (false :: l) = toNat.toNat' (List.length l -1) l := by
        simp [toNat.toNat', Bool.toNat]
      rw [u]
      rw [← Nat.mul_one (toNat.toNat' _ l), Nat.mul_assoc]
      apply Nat.mul_le_mul_left (toNat.toNat' _ l)
      simp
    | true =>
      simp [Nat.pow_succ]
      have u : toNat.toNat' (List.length l) (true :: l) = 2^(List.length l) + toNat.toNat' (List.length l - 1) l := by simp [toNat.toNat', Bool.toNat]
      have : 2^(List.length l)*2 = 2^(List.length l)+ 2^(List.length l) := by simp [Nat.mul_add, show 2 = 1+1 from rfl]
      rw [u, this]
      simp [ih, Nat.add_lt_add_left _ (2^(List.length l))]
  ⟩

@[simp] def toNat' (bs : List Bool) : {x : Nat // x < 2 ^ w} :=
  go w (bs.takeD w false).reverse
    ((bs.takeD w false).length_reverse ▸ (bs.takeD_length w false).symm)
where
  go (e : Nat) (bs : List Bool) (h : e = bs.length) : {x : Nat // x < 2 ^ e} :=
    match e, bs with
    | 0, [] => ⟨0, by decide⟩
    | e + 1, false :: bs =>
      let ⟨x, hx⟩ := go e bs (Nat.succ.inj h)
      ⟨x, Nat.lt_trans hx (Nat.pow_lt_pow_succ (by decide) _)⟩
    | e + 1, true :: bs  =>
      let ⟨x, hx⟩ := go e bs (Nat.succ.inj h)
      have : 2 ^ (e + 1) = 2 ^ e + 2 ^ e :=
        show 2 ^ e * (1 + 1) = _ from
        Nat.mul_add (2 ^ e) 1 1 ▸ Nat.mul_one _ ▸ rfl
      ⟨2 ^ e + x, this ▸ Nat.add_lt_add_left hx _⟩

def bbT' (bs : List Bool) : BitVec w :=
  ⟨(toNat' bs).1, (toNat' bs).2⟩


infix:30 " ^^ " => xor

namespace bit_add

variable {x y : BitVec w}

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

-- theorem add_bitblast {x y : BitVec w} {h: w > 0} : x + y = bit_add x y (h := h) := by
--   suffices goal: (x.val + y.val)%(2^w) = (bit_add x y (h := h)).val 
--   sorry
--   sorry

def toBool (x : BitVec w) (h : w > 0) :=
  (go (w - 1) (Nat.lt_self_sub_one h)).reverse
where
  go (i : Nat) (h: i < w) : List Bool := match i with
    | 0 => [x[0]]
    | i + 1 =>
      have h : i < w := Nat.lt_of_succ_lt h
      x[i+1] :: go i h
 
def toBool' (x w: Nat) :=
  (go (w - 1)).reverse
where
  go (i : Nat) : List Bool := match i with
    | 0 => [Nat.testBit x 0]
    | i + 1 =>
      Nat.testBit x (i+1) :: go i


lemma quotient_remainder_pow_2 (m n : Nat) : n = 2^m*Nat.shiftr n m + n%(2^m):= by
  rw [Nat.shiftr_eq_div_pow]
  simp [Nat.div_add_mod]

theorem helper_2 (x i : Nat) : x % 2 ^ (i + 1) = x % 2^i + 2^i * (Nat.testBit x i).toNat := by
  have h1 := quotient_remainder_pow_2 i x
  have h3 := Nat.div_add_mod (Nat.shiftr x i) 2
  cases' h : Nat.testBit x i
  · replace h : (Nat.shiftr x i)%2 = 0 := by
      unfold Nat.testBit at h
      simp [h, Nat.mod_two_of_bodd]
    rw [h, Nat.add_zero] at h3
    rw [← h3, ← mul_assoc, (show 2^i*2 = 2^(i+1) by rfl), add_comm] at h1
    simp [(Nat.div_mod_unique (NeZero.pos (2^(i+1)))).mpr ⟨Eq.symm h1, (show x%(2^i)<2^(i+1) by apply lt_trans (Nat.mod_lt x (NeZero.pos (2^i))); simp [Nat.pow_succ])⟩]
  · replace h : (Nat.shiftr x i)%2 = 1 := by
      unfold Nat.testBit at h
      simp [h, Nat.mod_two_of_bodd]
    rw [h, Nat.add_zero] at h3
    rw [← h3, mul_add, ← mul_assoc, (show 2^i*2 = 2^(i+1) by rfl), add_assoc, add_comm] at h1
    simp [(Nat.div_mod_unique (NeZero.pos (2^(i+1)))).mpr ⟨Eq.symm h1, (show 2^i*1 + x%(2^i) < 2^(i+1) by simp[Nat.add_lt_add_left, Nat.mod_lt x (NeZero.pos (2^i)), Nat.pow_succ, Nat.mul_two])⟩, Bool.toNat, add_comm]

#check List.length_eq_zero

theorem lt_pow_2_length {l : List Bool} (h: l.length = w) : toNat.toNat' w l < 2^w := by
  induction' l with b l' ih
  · aesop
  · unfold toNat.toNat'
    sorry

    

   
theorem toNat_toBool (x w: Nat) : x%(2^(w+1)) = toNat.toNat' w (toBool'.go x w) := by
  induction' w with w ih
  · simp [toBool'.go, toNat.toNat', Nat.mod_two_of_bodd, Nat.testBit]
    aesop
  · rw [helper_2, ih]
    simp [toNat.toNat', add_comm]


#eval toBool'.go (toNat.toNat' 5 ([false, false, true, true, true, true])) 5

#eval toBool'.go 10 5

#check List.ext
#eval [false, false, true, true, true, true].take 3
#eval toNat.toNat' 5 ([false, false, true, true, true, true])
#eval (toBool'.go 15 5).length
#eval Nat.testBit 15 4



#check List.ext_get

lemma toBool'_length (x w : Nat) : (toBool'.go x w).length = w+1 := by
  induction' w with w ih
  · simp [toBool'.go]
  · simp [toBool'.go, ih]
  

#check List.cons_getElem_succ

example (n: Nat) (h: n>0) : (n-1)+1 = n := by
  simp [Nat.sub_add_cancel h]

lemma toBool'_testBit (x i w: Nat) (h: i<(toBool'.go x w).length) : (toBool'.go x w)[i]= Nat.testBit x ((toBool'.go x w).length-(i+1))  := by
  induction' w with w iw
  · sorry
  · simp only [toBool'.go]
    sorry
    
    
    


theorem testBit_eq_scale_pow_two {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (x+2^w) i:= by
  simp only [Nat.testBit]
  rw [Nat.shiftr_eq_div_pow]
  rw [Nat.shiftr_eq_div_pow]
  suffices goal: (x/2^i)%2 = ((x+2^w)/2^i)%2 
  · simp [Nat.mod_two_of_bodd, cond] at goal
    aesop
  rw [Nat.add_div_of_dvd_left (by simp [Nat.pow_dvd_pow_iff_le_right, Nat.le_of_lt h]), Nat.add_mod]
  have h1: (2^w/2^i)%2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero]
    use 2^(w-(i+1))
    rw [Nat.pow_div (by linarith) (by decide)]
    nth_rewrite 2 [← pow_one 2]
    rw [← pow_add, add_comm]
    simp [← Nat.sub_add_comm, Nat.succ_le_of_lt h]
  · simp [h1, add_zero]



theorem toBool_toNat {l : List Bool} (h: 0<l.length):  toBool'.go (toNat.toNat' (l.length -1) l) (l.length -1) = l := by
  induction' l with b l' ih
  · simp at h
  · simp only [toBool'.go, toNat.toNat']
    apply List.ext_get
    · sorry
    · cases' Nat.eq_zero_or_pos (List.length l') with hl hl
      · sorry
      · intros n h1 h2
        rw [← List.getElem_eq_get]
        rw [← List.getElem_eq_get]
        rw [toBool'_testBit, Nat.add_comm]
        cases' Nat.eq_zero_or_pos n with h3 h3
        · simp [h3]
          sorry
        · cases' b
          <;> simp only [Bool.toNat, cond]
          · simp only [mul_zero, add_zero]
            sorry
          · rw [mul_one, toBool'_length, ← testBit_eq_scale_pow_two (by sorry)]
            rw [(show List.length (true :: l') - 1 - 1 = List.length l' - 1 by simp)]
            simp only [toBool'.go] at ih
            have h4: n < List.length (toBool'.go (toNat.toNat' (List.length l' - 1) l') (List.length l' - 1)) := by sorry
            rw [List.length_cons] at h2
            have iH: (toBool'.go (toNat.toNat' (List.length l' - 1) l') (List.length l' - 1))[n-1]'(tsub_lt_of_lt h4)= l'[n-1]'(tsub_lt_tsub_right_of_le (by linarith) h2) := by
              simp [ih hl]
            rw [toBool'_testBit, toBool'_length] at iH
            rw [show List.length l' - 1 + 1 - (n - 1 + 1) = List.length l' - n by sorry] at iH
            rw [show List.length (true :: l') - 1 + 1 - (n + 1) = List.length l' - n by simp]
            rw [iH]
            suffices goal: l'[n-1]'(show n-1 < l'.length by sorry) = (true::l')[n-1+1]'(by sorry)
            · rw [goal, Nat.sub_add_cancel (show 1 ≤ n by sorry)]
            exact List.cons_getElem_succ true l' (n-1) (by sorry)

theorem inv_bbT_toBool (x : BitVec w) (h : w > 0) : (bbT' (toBool x h)) = x := by
  induction' w, h using Nat.le_induction with w h hw
  · simp only [toBool, toBool.go]
    have h1: x[0] = true ∨ x[0] = false := by 
      cases' x[0]
      <;> simp
    have h2:= x.isLt
    apply Fin.eq_of_val_eq
    


    cases' h1 with ht hf
    · rw [ht]
      simp [bbT', toNat', toNat'.go]
      sorry
      



      

    · sorry



    
  · sorry



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


def carry''' (x y : Nat) (i : Nat) : Bool := match i with
  | 0     => false
  | i + 1 =>
    (Nat.testBit x i && Nat.testBit y i) || ((Nat.testBit x i ^^ Nat.testBit y i) && carry''' x y i)


def go'5 (x y i : Nat) : List Bool := match i with
  | 0     => [(Nat.testBit x 0 ^^ Nat.testBit y 0) ^^ @carry''' x y 0]
  | i + 1 =>
  ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ @carry''' x y (i + 1)) :: @go'5 x y i
    


def go''' (x y z i : Nat) : Nat := match i with
  | 0     => Nat.bit ((Nat.testBit x 0 ^^ Nat.testBit y 0) ^^ carry''' x y 0) z
  | i + 1 =>
    go''' x y (Nat.bit ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1)) z) i


#eval go''' 15 14 0 4
#eval toNat.toNat' 4 (go'5 15 14 4)

#eval Nat.bit true 0

lemma bit_0 (b : Bool) : Nat.bit b 0 = b.toNat := by
  cases' b <;> simp

lemma bit_1 (b : Bool) (n : Nat) : Nat.bit b 1 = 2+b.toNat:= by
  cases' b <;> simp

lemma foo : 2^(i+1) = 2^i + 2^i := by
  sorry

lemma helper_0 {x y : Nat} {b: Bool}: go''' x y b.toNat i = 2 ^ (i + 1)*b.toNat + go''' x y 0 i := by
  cases b
  · simp [go''', Bool.toNat]
  · simp only [go''', Bool.toNat, cond, mul_one]
    induction' i with i ih
    · sorry
    · unfold go'''
      rw [bit_0, bit_1]
      cases' (Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1)
      · simp only [Bool.toNat, cond, add_zero]
        rw [foo, add_assoc, ← ih]
        sorry
      · sorry
      sorry

    
    

#eval toNat.toNat' 2 (go'5 15 14 2)
#eval go''' 15 14 0 2 + 2^3
#eval go''' 15 14 1 2

theorem go'5_eq_go''' (x y w: Nat) : toNat.toNat' w (go'5 x y w) = go''' x y 0 w := by
  induction' w with w ih
  · simp [go'5, go''', bit_0, toNat.toNat']
  · simp only [toNat.toNat', go''', (show Nat.succ w - 1 = w by simp)]
    rw [ih, bit_0, helper_0]

    


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

@[simp] def bool_to_nat (b : Bool) : Nat := match b with
  | true => 1
  | false => 0

lemma xor_mod_2 (a b : Bool) : toNat [a ^^ b] = (toNat [a] + toNat [b])%2 := by
  cases' a
  · cases' b
    · simp
    · simp
  · cases' b
    · simp
    · simp

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

theorem eq_bv (h: v < 2^w): (BitVec.ofNat w v).val = v := by
  simp [BitVec.ofNat]
  norm_cast
  exact Nat.mod_eq_of_lt h
  
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

   


lemma xor_mod_2'' (a b : Bool) : (a ^^ b).toNat = (a.toNat + b.toNat)%2 := by
  cases' a
  · cases' b
    · simp
    · simp
  · cases' b
    · simp
    · simp

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


lemma unfold_carry''' (x y i : Nat) : (carry''' x y (i+1)).toNat = ((Nat.testBit x i && Nat.testBit y i) || ((Nat.testBit x i ^^ Nat.testBit y i) && carry''' x y i)).toNat := by
  simp [carry''']

theorem go'5_correct (x y i: Nat) : x%(2^(i+1)) + y%(2^(i+1)) = toNat.toNat' i (go'5 x y i) + 2^(i+1)*(carry''' x y (i+1)).toNat := by
  induction' i with i hi
  · simp [toNat.toNat', carry''']
    cases' hx: Nat.bodd x 
    <;> cases' hy: Nat.bodd y
    <;> simp [Nat.mod_two_of_bodd, Nat.testBit, hx, hy, Nat.shiftr]
  · simp only [toNat.toNat']
    rw [show Nat.succ i - 1 = i by simp]
    rw [helper_2 x, helper_2 y]
    suffices goal: (x % 2 ^ (i + 1) + y % 2 ^ (i + 1)) + 2 ^ (i + 1) * Bool.toNat (Nat.testBit x (i + 1))  +  2 ^ (i + 1) * Bool.toNat (Nat.testBit y (i + 1)) = 2 ^ Nat.succ i * Bool.toNat ((Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1)) +
      toNat.toNat' i (go'5 x y i) +
    2 ^ (Nat.succ i + 1) * Bool.toNat (carry''' x y (Nat.succ i + 1))
    · rw [← goal]
      ring
    rw [hi]
    rw [unfold_carry''' x y (Nat.succ i)]
    rw [pow_succ 2 (Nat.succ i), two_mul, add_mul]
    cases' hx : Nat.testBit x (i+1) 
    <;> cases' hy : Nat.testBit y (i+1) 
    <;> cases' hc : carry''' x y (i+1) 
    <;> simp [Nat.add_left_cancel_iff, Nat.succ_eq_add_one, Nat.add_comm]
    <;> ring

theorem bit_add_finally (x y i : Nat): (x+y)%(2^(i+1)) = toNat.toNat' i (go'5 x y i) := by
  rw [Nat.add_mod, go'5_correct]
  suffices goal : toNat.toNat' i (go'5 x y i) < 2^(i+1) 
  · simp [Nat.mod_eq_of_lt, goal]
  sorry





theorem testBit_add (x y : Nat)(h : i<x): (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ carry''' x y i):= by
  have h1: x%2^(y+1) = x := by sorry
  have h2: y%2^(y+1) = y := by sorry
  nth_rewrite 1 [← h1]
  nth_rewrite 2 [← h2]
  rw [go'5_correct]
  sorry



  

    
    
    

    

    












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



    








-- theorem go'''_correct (x y : Nat) : go''' x y 0 i = (x + y) % 2 ^ (i + 1) := by
--   induction' i with i hi
--   · simp [go''']
--     sorry  
--   · unfold go'''

--     cases' h : (Nat.testBit x (i + 1) ^^ Nat.testBit y (i + 1)) ^^ carry''' x y (i + 1) with h1 h2
--     · simp
--       rw [hi]
--       rw [helper_2 (x+y) (i+1)]
      
--       have h := helper_1 h
--       apply helper_2 h
--     · simp
--       rw [helper_0, hi]
--       sorry




         
  
  -- have H1 := hi (x - 2 ^ i * bool_to_nat (Nat.testBit x i)) (y - 2 ^ i * bool_to_nat (Nat.testBit y i)) (descend_bv_pre''' i x hx) (descend_bv_pre''' i y hy)
  --   unfold go'''
    

-- theorem bit_add'''_bitblast {h : w > 0} : (x + y).val = (bit_add''' x y).val := by
--   have ⟨x, hx⟩ := x
--   have ⟨y, hy⟩ := y
--   simp only [bit_add''', HAdd.hAdd, Add.add, BitVec.add, Fin.add]
--   rw [go'''_correct x y]
--   sorry





-- end BitVec