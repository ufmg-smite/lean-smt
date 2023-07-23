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
  let [mv] ← mv.apply (mkConst ``val_bitvec_eq)
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


#check mod_two_pow_succ
#check Nat.mul_mod_mul_right
#check shiftLeft_eq
theorem bv_rotate_left_eliminate₁ {x : BitVec (w +1)} (h : a % (w + 1) ≠ 0) : 
  (BitVec.rotateLeft x (a%(w + 1))).val = (BitVec.extract (w + 1 - (1 + a%(w+1))) 0 x ++ BitVec.extract w (w+1 - a%(w + 1)) x).val := by
  have h1: ShiftRight.shiftRight x.val 0 = x.val := sorry
  simp only [rotateLeft, concat_ext, xor_ext]
  rw [extract_val (lt_succ_iff.mp (tsub_lt_self (succ_pos w) (pos_iff_ne_zero.mpr h)))]
  congr
  simp only [HShiftRight.hShiftRight, BitVec.shiftRight, extract]
  simp only [BitVec.ofNat, Fin.ofNat', shiftLeft_eq]
  have h2 : w + 1 - (1 + a % (w + 1)) - 0 + 1 = w + 1 - a%(w + 1) := sorry
  have h3 : w - (w + 1 - a % (w + 1)) + 1 = a % (w + 1) := sorry
  rw [h1, h2, h3]
  



end Smt.Reconstruction.Rewrites.Arith
