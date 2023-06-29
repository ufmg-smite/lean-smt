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
    simp only [HAppend.hAppend, BitVec.append, add_comm b c, append_eq_add (concat_size z.isLt y.isLt)]
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
  simp only [bv_extract_ext, bVappend_eq_add]
  rw [mul_comm, add_comm]
  apply @And.left _ ((x.val/2^i) % 2^(j-i+1)< 2^(j-i+1)) _
  rw [← Nat.div_mod_unique (two_pow_pos (j-i+1))]
  apply And.intro _ (mod_mod_of_dvd _ (pow_dvd_pow 2 (by zify [*, (show i ≤ k by linarith)]; linarith)))
  simp only [div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  · congr 1; zify [*, (show i ≤ k by linarith)]; ring
  · zify [*]; ring

  
-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/bv/rewrites

-- Core Normalization Rules --

@[smt_simp] theorem bv_concat_flatten {xs : BitVec a} {s : BitVec b} {ys : BitVec c} {zs : BitVec d} :
  (xs ++ (s ++ ys) ++ zs).val = (xs ++ s ++ ys ++ zs).val :=
  bVappend_eq_add ▸ bVappend_eq_add (x := xs ++ s ++ ys) ▸ append_assoc ▸ rfl

@[smt_simp] theorem bv_concat_extract_merge {xs : BitVec a} {s : BitVec b} {ys : BitVec c} {i j k : Nat} (hik : i ≤ k) (hjk : j + 1 ≤ k) (hij : i ≤ j) :
  (xs ++ s.extract k (j + 1) ++ s.extract j i ++ ys).val = (xs ++ s.extract k i ++ ys).val := by
  rewrite [bVappend_eq_add (x := xs ++ s.extract k i)]
  rewrite [bVappend_eq_add (y := s.extract k i)]
  rw [←bv_extract_concat_eq hjk hij]
  rewrite [t]
  simp only [←bVappend_eq_add, ←append_assoc]
where
  t : k - i + 1 = k - (j + 1) + 1 + (j - i + 1) := by
    zify [hik, hjk, hij]
    linarith

-- x[i:j] ++ x[k:l] = x[i+k:i+l]
@[smt_simp] theorem bv_extract_extract {x : BitVec w} {hl : k ≤ l} {hk : l ≤ j - i}: ((x.extract j i).extract l k).val = (x.extract (i + l) (i + k)).val := by
  simp only [bv_extract_ext, div_mod_eq_mod_mul_div, Nat.div_div_eq_div_mul, ← pow_add]
  rw [mod_mod_of_dvd _ (by apply pow_dvd_pow; zify [*]; linarith)]
  congr 3; zify [hl, hk, add_le_add_left hl]; ring



-- the intended h was w - 1 ≤ n...
@[smt_simp] theorem bv_extract_whole {x : BitVec w} {h : w ≤ n + 1} : (x.extract n 0).val = x.val := by
  rw [← val_to_ofNat (lt_of_lt_of_le x.isLt (pow_le_pow_of_le_right (by decide) h)), extract]
  simp [shiftRight_eq_shiftr, shiftr_eq_div_pow]

-- Case 1: j < a so the extract is self contained
@[smt_simp] theorem bv_extract_concat_1 {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hij: i ≤ j) (hja : j < a) : ((xs ++ y ++ x).extract j i).val = (x.extract j i).val := by
   simp only [bv_extract_ext, bVappend_eq_add]
   have h1 : 2^(j-i+1) ∣ 2^a / 2^i ∧ 2^i ∣ 2^a:= by
    simp only [pow_div (show i ≤ a by linarith), pow_dvd_pow_iff_le_right]
    zify [*, (show i ≤ a by linarith)]; rw [and_true]; linarith
   rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_right (h1.2) _), Nat.mul_div_assoc _ h1.2]
   cases' h1.1 with l hl; rw[hl, mul_comm _ l,← mul_assoc] --shouldnt have to do this.
   rw [Nat.mul_add_mod]


-- Case 2: j ≥ a so the extract is not self contained
@[smt_simp] theorem bv_extract_concat_2 {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hia: i < a) (hja : a ≤ j) (ha : 0 < a) : 
((xs ++ y ++ x).extract j i).val = (((xs ++ y).extract (j-a) 0) ++ (x.extract (a - 1) i)).val := by
  rw [← bv_extract_concat_eq ((Nat.sub_add_cancel (one_le_of_lt ha)).symm ▸ hja) (le_pred_of_lt hia)]
  simp only [bVappend_eq_add]
  rw [bv_extract_concat_1 (le_pred_of_lt hia) (Nat.sub_lt ha _)]
  congr 2; swap; decide
  simp only [bv_extract_ext, bVappend_eq_add, Nat.sub_add_cancel (one_le_of_lt ha)]
  rw [add_comm, add_mul_div_right _ _ (two_pow_pos a), Nat.div_eq_zero x.isLt]
  simp


-- Case 3: i ≥ a and j ≥ a, extract elides x
@[smt_simp] theorem bv_extract_concat_3 {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hia : a ≤ i) (hij: i ≤ j):
  ((xs ++ y ++ x).extract j i).val = ((xs ++ y).extract (j - a) (i - a)).val := by
  have : x.val < 2^i := lt_of_lt_of_le x.isLt (pow_le_pow_of_le_right (by decide) hia)
  have h0 : 2^i = 2^(i-a) * 2^a := by rw [← pow_add]; congr 1; zify [hia]; linarith
  simp only [bv_extract_ext, bVappend_eq_add]
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
theorem bv_extract_concat_4 {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hij: i ≤ j) (hj : j < b+ c) : ((x ++ xs ++ y).extract j i).val = ((xs ++ y).extract j i).val := by
  simp only [bv_extract_ext, bVappend_eq_add]
  have h1 : 2^(j-i+1) ∣ 2^(b+c)/2^i ∧ 2^i ∣ 2^(b+c) := by
    simp only [pow_div (show i ≤ b+c by linarith), pow_dvd_pow_iff_le_right]
    zify [*, (show i ≤ b+c by linarith)]; rw [and_true]; linarith
  rw [add_mul, mul_assoc, ← pow_add, add_assoc, ]
  rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_right (h1.2) _), Nat.mul_div_assoc _ h1.2]
  cases' h1.1 with l hl; rw[hl, mul_comm _ l, ← mul_assoc] --shouldnt have to do this. 
  rw [Nat.mul_add_mod]




end Smt.Reconstruction.Rewrites.Arith
