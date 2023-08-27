/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman Mohamed
-/

import Mathlib
import Smt.Data.BitVec
import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Arith

open BitVec Nat

theorem eq_bv_of_eq_val {x y : BitVec w} (h : x.val = y.val) : x = y := sorry

theorem append_assoc {x : BitVec a} {y : BitVec b} {z : BitVec c} :
  ((x ++ y) ++ z).val = (x ++ (y ++ z)).val := by
    simp only [HAppend.hAppend, BitVec.append, add_comm b c, append_eq_add (append_lt z.isLt y.isLt)]
    simp only [append_eq_add _, y.isLt, x.isLt, z.isLt]
    ring

theorem append_assoc' {x : BitVec a} {y : BitVec b} {z : BitVec c} :
  ((x ++ y) ++ z) = Nat.add_assoc _ _ _ ▸ (x ++ (y ++ z)) := by
    rw [← val_bitvec_eq, BitVec.cast_heq, append_assoc]

open Lean

/-- Prove equality theorem for concrete size bit-vectors -/
def concreteSize (mv : MVarId) (heq : Expr) : MetaM Unit := do
  let [mv] ← mv.apply (mkConst ``eq_bv_of_eq_val)
    | throwError "failed to apply `eq_bv_of_eq_val`"
  let r ← mv.rewrite (← mv.getType) heq false (.pos [1])
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  mv.refl

/-- The `concrete_size` tactic. -/
syntax (name := bv_append_assoc) "concrete_size" ident : tactic

open Elab Tactic in
/-- Implementation of the `bv_append_assoc` tactic. -/
@[tactic bv_append_assoc] def evalBVAppendAssoc : Tactic := fun stx => do
  let mv ← Tactic.getMainGoal
  concreteSize mv (← elabTerm stx[1] none)
  Tactic.replaceMainGoal []
  
lemma comm_bv {x : BitVec b} {y : BitVec b}: (x++y++y).val = (y ++ x++x).val := sorry

example {x y z: BitVec 10}: x ++ y++y = y ++ x++x := by
  concrete_size comm_bv

-- the apply And.left is quite weird.
theorem bv_extract_concat_eq {x : BitVec w} (hjk : j + 1 ≤ k) (hij : i ≤ j):  (x.extract k (j + 1) ++ x.extract j i).val = (x.extract k i).val := by
  simp only [extract_ext, append_eq_add_val]
  rw [mul_comm, add_comm]
  apply @And.left _ ((x.val/2^i) % 2^(j-i+1)< 2^(j-i+1)) _
  rw [← Nat.div_mod_unique (two_pow_pos (j-i+1))]
  apply And.intro _ (mod_mod_of_dvd _ (pow_dvd_pow 2 (by zify [*, (show i ≤ k by linarith)]; linarith)))
  simp only [div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  · congr 1; zify [*, (show i ≤ k by linarith)]; ring
  · zify [*]; ring

  
-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/bv/rewrites

/-! ### Core Normalization Rules -/

@[smt_simp] theorem bv_concat_flatten {xs : BitVec a} {s : BitVec b} {ys : BitVec c} {zs : BitVec d} :
  (xs ++ (s ++ ys) ++ zs).val = (xs ++ s ++ ys ++ zs).val :=
  append_eq_add_val ▸ append_eq_add_val (x := xs ++ s ++ ys) ▸ append_assoc ▸ rfl

@[smt_simp] theorem bv_concat_extract_merge {xs : BitVec a} {s : BitVec b} {ys : BitVec c} {i j k : Nat} (hik : i ≤ k) (hjk : j + 1 ≤ k) (hij : i ≤ j) :
  (xs ++ s.extract k (j + 1) ++ s.extract j i ++ ys).val = (xs ++ s.extract k i ++ ys).val := by
  rewrite [append_eq_add_val (x := xs ++ s.extract k i)]
  rewrite [append_eq_add_val (y := s.extract k i)]
  rw [←bv_extract_concat_eq hjk hij]
  rewrite [t]
  simp only [← append_eq_add_val, ←append_assoc]
where
  t : k - i + 1 = k - (j + 1) + 1 + (j - i + 1) := by
    zify [hik, hjk, hij]
    linarith

-- x[i:j] ++ x[k:l] = x[i+k:i+l]
@[smt_simp] theorem bv_extract_extract {x : BitVec w} {hl : k ≤ l} {hk : l ≤ j - i}: ((x.extract j i).extract l k).val = (x.extract (i + l) (i + k)).val := by
  simp only [extract_ext, div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]
  rw [mod_mod_of_dvd _ (by apply pow_dvd_pow; zify [*]; linarith)]
  congr 3; zify [hl, hk, add_le_add_left hl]; ring



-- the intended h was w - 1 ≤ n...
@[smt_simp] theorem bv_extract_whole {x : BitVec w} {h : w ≤ n + 1} : (x.extract n 0).val = x.val := by
  rw [← val_to_ofNat (lt_of_lt_of_le x.isLt (pow_le_pow_of_le_right (by decide) h)), extract]
  simp [shiftRight_eq_shiftr, shiftr_eq_div_pow]

-- Case 1: j < a so the extract is self contained
@[smt_simp] theorem bv_extract_concat₁ {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hij: i ≤ j) (hja : j < a) : ((xs ++ y ++ x).extract j i).val = (x.extract j i).val := by
   simp only [extract_ext, append_eq_add_val]
   have h1 : 2^(j-i+1) ∣ 2^a / 2^i ∧ 2^i ∣ 2^a:= by
    simp only [pow_div (show i ≤ a by linarith), pow_dvd_pow_iff_le_right]
    zify [*, (show i ≤ a by linarith)]; rw [and_true]; linarith
   rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_right (h1.2) _), Nat.mul_div_assoc _ h1.2]
   cases' h1.1 with l hl; rw[hl, mul_comm _ l,← mul_assoc] --shouldnt have to do this.
   rw [Nat.mul_add_mod]


-- Case 2: j ≥ a so the extract is not self contained
@[smt_simp] theorem bv_extract_concat₂ {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hia: i < a) (hja : a ≤ j) (ha : 0 < a) : 
((xs ++ y ++ x).extract j i).val = (((xs ++ y).extract (j-a) 0) ++ (x.extract (a - 1) i)).val := by
  rw [← bv_extract_concat_eq ((Nat.sub_add_cancel (one_le_of_lt ha)).symm ▸ hja) (le_pred_of_lt hia)]
  simp only [append_eq_add_val]
  rw [bv_extract_concat₁ (le_pred_of_lt hia) (Nat.sub_lt ha _)]
  congr 2; swap; decide
  simp only [extract_ext, append_eq_add_val, Nat.sub_add_cancel (one_le_of_lt ha)]
  rw [add_comm, add_mul_div_right _ _ (two_pow_pos a), Nat.div_eq_zero x.isLt]
  simp


-- Case 3: i ≥ a and j ≥ a, extract elides x
@[smt_simp] theorem bv_extract_concat₃ {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hia : a ≤ i) (hij: i ≤ j):
  ((xs ++ y ++ x).extract j i).val = ((xs ++ y).extract (j - a) (i - a)).val := by
  have : x.val < 2^i := lt_of_lt_of_le x.isLt (pow_le_pow_of_le_right (by decide) hia)
  have h0 : 2^i = 2^(i-a) * 2^a := by rw [← pow_add]; congr 1; zify [hia]; linarith
  simp only [extract_ext, append_eq_add_val]
  rw [add_div_eq_of_add_mod_lt]
  · congr 1
    · rw [Nat.div_eq_zero this, h0]
      simp [Nat.mul_div_mul_right _ _ (two_pow_pos a)]
    · congr 1 ; zify [*, tsub_le_tsub_right hij a, le_trans hia hij]; simp
  · rw [mod_eq_of_lt this]
    have h1 : 2^a ∣ (xs.val * 2 ^ c + y.val) * 2 ^ a % 2 ^ i := by
      simp [dvd_of_mod_eq_zero, Nat.mod_mod_of_dvd _  (pow_dvd_pow _ hia)]
    cases' h1 with l hl; rw [hl]
    have h2: 2^a*l < 2^i := by rw [← hl]; exact Nat.mod_lt _ (two_pow_pos _)
    rw [mul_comm, h0, mul_lt_mul_right (two_pow_pos a)] at h2
    calc 2^a * l + x.val ≤  2^a * (2^(i-a) - 1) + x.val  := by simp [Nat.le_pred_of_lt h2]
         _ < 2^a * (2^(i-a) - 1) + 2^a := by simp [x.isLt]
         _ = 2^i := by zify [one_le_of_lt (two_pow_pos (i-a))] at *; linarith [h0]
    

-- Case 4: Elision from the higher portion
@[smt_simp] theorem bv_extract_concat₄ {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hij: i ≤ j) (hj : j < b+ c) : ((x ++ xs ++ y).extract j i).val = ((xs ++ y).extract j i).val := by
  simp only [extract_ext, append_eq_add_val]
  have h1 : 2^(j-i+1) ∣ 2^(b+c)/2^i ∧ 2^i ∣ 2^(b+c) := by
    simp only [pow_div (show i ≤ b+c by linarith), pow_dvd_pow_iff_le_right]
    zify [*, (show i ≤ b+c by linarith)]; rw [and_true]; linarith
  rw [add_mul, mul_assoc, ← pow_add, add_assoc, ]
  rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_right (h1.2) _), Nat.mul_div_assoc _ h1.2]
  cases' h1.1 with l hl; rw[hl, mul_comm _ l, ← mul_assoc] --shouldnt have to do this. 
  rw [Nat.mul_add_mod]

/-! ### Operator Elimination Rules -/

theorem bv_ugt_eliminate {x y : BitVec w} : (x > y) = (y < x) := by simp

theorem bv_uge_eliminate {x y : BitVec w} : (x ≥ y) = (y ≤ x) := by simp

lemma signed_bit : (x + 2^w).testBit w = !x.testBit w := by
  simp only [testBit, shiftr_eq_div_pow, bodd_neq_mod_two, add_div_right _ (two_pow_pos w)]
  cases' mod_two_eq_zero_or_one (x/2^w) with h1 h1
  <;> simp [h1, succ_eq_add_one, add_mod]

theorem bv_slt_eliminate {x y : BitVec (w + 1)} : (BitVec.slt x y) = ((x.val + 2^(w))%(2^(w+1)) < (y.val + 2^(w))%(2^(w+1))) := by
  simp only [mod_two_pow_succ, signed_bit]
  simp only [BitVec.slt, testBit_eq_shift, y.isLt, x.isLt]
  cases' b : x.val.testBit w <;> cases' b' : y.val.testBit w
  <;> simp [mod_lt _ (two_pow_pos w), Nat.lt_add_right, le_of_lt]

theorem bv_sle_eliminate {x y : BitVec (w + 1)} : (BitVec.sle x y) = ¬ BitVec.slt y x := by
  simp only [BitVec.slt, BitVec.sle, if_true_left_eq_or]
  push_neg
  simp only [le_iff_lt_or_eq]
  aesop

theorem bv_ule_eliminate {x y : BitVec w} : (x ≤ y) = ¬ (y < x) := by 
  simp [LT.lt, BitVec.lt, LE.le, BitVec.le]

theorem bv_sub_eliminate {x y : BitVec w} : (x - y) = x + (-y) := by 
  simp only [BitVec.sub, Fin.sub, Neg.neg, BitVec.neg, HAdd.hAdd, Add.add, BitVec.add, Fin.add]
  aesop

theorem bv_repeat_eliminate₁ {x : BitVec w} : 
  BitVec.repeat_ (n + 1) x = (show w*(n + 1) = w + w*n by ring) ▸ (x ++ (BitVec.repeat_ n x)) := by
  simp [repeat_]; aesop

theorem bv_repeat_eliminate₂ {x : BitVec w} : 
  BitVec.repeat_ 1 x = (show w = w*1 by simp) ▸ x := by
  simp [repeat_, eq_rec_inj, ← val_bitvec_eq, BitVec.append_eq_add_val]

theorem extract_val {x : BitVec (w + 1)} (h : j ≤ w) : (BitVec.extract w j x).val = x.val >>> j := by
  simp only [BitVec.ofNat, Fin.ofNat', extract]
  rw [mod_eq_of_lt]
  rw [shiftRight_eq_shiftr, shiftr_eq_div_pow, ← Nat.sub_add_comm h]
  rw [← pow_div (by linarith) (by decide)]
  exact Nat.div_lt_div_of_lt_of_dvd ((Nat.pow_dvd_pow_iff_le_right (by decide)).mpr (by linarith)) x.isLt

lemma shiftRight_zero : m >>> 0 = m := rfl

theorem extract_val' {x : BitVec w} : (BitVec.extract j 0 x).val = x.val % 2^(j + 1) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_zero]

theorem bv_rotate_left_eliminate₁ {x : BitVec (w +1)} (h0 : 0 < a) (ha : a < w + 1) : 
  (BitVec.rotateLeft x a).val = (BitVec.extract (w + 1 - (1 + a)) 0 x ++ BitVec.extract w (w+1 - a) x).val := by
  simp only [rotateLeft, concat_ext, or_ext, shiftLeft_ext, shiftLeft_eq, shiftRight_ext]
  rw [extract_val (lt_succ_iff.mp (tsub_lt_self (succ_pos w) h0))]; congr
  simp only [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_shiftr, shiftr_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have h2 : w + 1 - (1 + a) - 0 + 1 = w + 1 - a := by 
    rw [Nat.sub_zero]; zify [(show 1 + a ≤ w + 1 by linarith), le_of_lt ha]; linarith
  have h3 : w - (w + 1 - a) + 1 = a := by 
    zify [succ_sub_one w ▸ tsub_le_tsub_left (one_le_of_lt h0) (w + 1), le_of_lt ha]; linarith
  rw [h2, h3, ← mul_mod_mul_right, ← pow_add, Nat.sub_add_cancel (by linarith)]

--this proof should be alot quicker! It's just unfolding definitions!
theorem bv_rotate_left_eliminate₂ {x : BitVec (w + 1)} : (BitVec.rotateLeft x 0).val = x.val := by
  simp only [rotateLeft, or_ext, shiftLeft_ext, shiftLeft_eq, shiftRight_ext, Nat.sub_zero]
  simp only [shiftRight_eq_shiftr, shiftr_eq_div_pow, Nat.div_eq_zero x.isLt]
  simp [HOr.hOr, OrOp.or, lor, bitwise_eq_bitwise', bitwise'_zero_right, mod_eq_of_lt x.isLt]

theorem rotate_right_rotate_left {x : BitVec w} (h : a ≤ w) : (rotateRight x a).val = (rotateLeft x (w-a)).val := by
  simp only [rotateRight, rotateLeft, HOr.hOr, OrOp.or, lor, BitVec.or, bitwise_eq_bitwise']
  rw [bitwise'_comm (fun b b' => by cases' b <;> cases' b' <;> simp) (by simp)]; congr --so long!
  zify[h, tsub_le_self]; linarith

theorem bv_rotate_right_eliminate₁ {x : BitVec (w + 1)} (h0 : 0 < a) (ha : a < w + 1) : 
  (BitVec.rotateRight x a).val = (BitVec.extract (a - 1) 0 x ++ BitVec.extract w a x).val := by
  rw [rotate_right_rotate_left (le_of_lt ha)]
  rw [bv_rotate_left_eliminate₁ (Nat.sub_pos_of_lt ha) (Nat.sub_lt (succ_pos w) h0), concat_ext, concat_ext]
  have H : w + 1 - (w + 1 - a) = a := by
    zify [le_of_lt ha, Nat.sub_le]; ring
  have H1 := add_comm 1 w ▸ add_eq ▸ (le_of_lt_succ (add_lt_add_left (sub_lt (succ_pos w) h0) 1))
  have H2 : w + 1 - (1 + (w + 1 - a)) = a - 1 := by
    zify [le_of_lt ha, h0, H1]
    ring
  simp only [H, extract_val', H2]
  congr

--this proof should be alot quicker! It's just unfolding definitions!
theorem bv_rotate_right_eliminate₂ {x : BitVec (w + 1)} : (BitVec.rotateRight x 0).val = x.val := by
  simp only [rotateRight, or_ext, shiftLeft_ext, shiftLeft_eq, shiftRight_ext, Nat.sub_zero]
  simp only [shiftRight_eq_shiftr, shiftr_eq_div_pow, Nat.div_eq_zero x.isLt]
  simp [HOr.hOr, OrOp.or, lor, bitwise_eq_bitwise', bitwise'_zero_right, mod_eq_of_lt x.isLt]


def bv_nand (x y : BitVec w) := ~~~ (x &&& y)

def bv_nor (x y : BitVec w) := ~~~ (x ||| y)

def bv_xnor (x y : BitVec w) := ~~~ (x ^^^ y)

def bv_xnor' (x y : BitVec w) : BitVec w := 
  ⟨toNat (fun i => x.val.testBit i == y.val.testBit i) 0 w, toNat_lt⟩ 

theorem bitwise_not_eq_not {x : BitVec (w + 1)} : bitwise_not x.val (w + 1) = (~~~x).val := by
  simp only [Complement.complement, BitVec.complement, sub_ext, add_ext]
  have H := one_lt_two_pow _ (succ_pos w)
  rw [val_to_ofNat H, zero_ext, zero_add]
  apply (add_left_inj x.val).mp
  rw [bitwise_not_eq_neg_sub_one x.isLt]
  cases' eq_or_lt_of_le (show x.val + 1 ≤ 2^(w + 1) by linarith [x.isLt]) with h h
  · simp [← h]
  · rw [mod_eq_of_lt h, mod_eq_of_lt (sub_lt (two_pow_pos _) (succ_pos _))]
    zify [le_of_lt H, le_of_lt h]; linarith
  

theorem xor_eq_xor' {m n : Nat} : m ^^^ n = Nat.lxor' m n := by
  simp only [Nat.xor, bitwise_eq_bitwise' bne (by simp), HXor.hXor, Xor.xor, lxor']
  congr; aesop

theorem bv_xnor_eliminate {x y : BitVec (w + 1)} : (bv_xnor' x y).val = (bv_xnor x y).val := by
  simp only [bv_xnor', bv_xnor, ← bitwise_not_eq_not, bitwise_not]
  apply eq_of_testBit_eq_lt toNat_lt toNat_lt; intro j hj
  rw [toNat_testBit hj, toNat_testBit hj, xor_ext, xor_eq_xor', lxor']
  simp [testBit_bitwise']
  cases' x.val.testBit j <;> cases' y.val.testBit j <;> simp

def bv_sdiv {x y : BitVec (w + 1)} := 
  let xlt0 := x.extract w w ==  BitVec.ofNat (w - w + 1) 1
  let ylt0 := y.extract w w == BitVec.ofNat (w - w + 1) 1
  let rUdiv := (UdivUremBB (if xlt0 then (~~~x).val else x.val) (if ylt0 then (~~~y).val else y.val) (w + 1)).snd
  let rUdivbv := BitVec.ofNat (w + 1) rUdiv
  if (xlt0 ^^ ylt0) then (~~~ rUdivbv) else rUdivbv
  
end Smt.Reconstruction.Rewrites.Arith