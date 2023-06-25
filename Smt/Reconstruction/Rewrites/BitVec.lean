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




-- Case 1: j ≤ a so the extract is self contained
@[smt_simp] theorem bv_extract_concat_1 {x : BitVec a} {xs : BitVec b} {y : BitVec c} {i j : Nat} (hij: i ≤ j) (hja : j < a) : ((xs ++ y ++ x).extract j i).val = (x.extract j i).val := by
   simp only [bv_extract_ext, bVappend_eq_add]
   have h1 : 2^(j-i+1) ∣ 2^a / 2^i ∧ 2^i ∣ 2^a:= by
    simp only [pow_div (show i ≤ a by linarith), pow_dvd_pow_iff_le_right]
    zify [*, (show i ≤ a by linarith)]; rw [and_true]; linarith
   rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_right (h1.2) _), Nat.mul_div_assoc _ h1.2]
   cases' h1.1 with l hl; rw[hl, mul_comm _ l,← mul_assoc]
   rw [Nat.mul_add_mod]




end Smt.Reconstruction.Rewrites.Arith
