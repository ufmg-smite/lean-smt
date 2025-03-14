/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Real.Basic

namespace Smt.Arith

theorem lt_eq_sub_lt_zero [LinearOrderedRing α] {a b : α} : (a < b) = (a - b < 0) := by
  simp only [sub_neg]

theorem le_eq_sub_le_zero [LinearOrderedRing α] {a b : α} : (a ≤ b) = (a - b ≤ 0) := by
  simp only [tsub_le_iff_right, zero_add]

theorem eq_eq_sub_eq_zero [LinearOrderedRing α] {a b : α} : (a = b) = (a - b = 0) := by
  simp only [sub_eq_zero]

theorem ge_eq_sub_ge_zero [LinearOrderedRing α] {a b : α} : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, sub_nonneg]

theorem gt_eq_sub_gt_zero [LinearOrderedRing α] {a b : α} : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, sub_pos]

theorem lt_of_sub_eq [LinearOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : α} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero _ _ b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq [LinearOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : α} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero _ _ b₁, ← this hc₁, ← this hc₂, h]

theorem eq_of_sub_eq [LinearOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  have {c x y : α} (hc : c > 0) : (c * (x - y) = 0) = (x - y = 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c] --, mul_right_inj' (ne_of_gt hc)]
    simp only [mul_zero, mul_eq_zero, eq_iff_iff, or_iff_right_iff_imp]
    intro abs
    rw [abs] at hc
    simp only [gt_iff_lt, lt_self_iff_false] at hc
  rw [@eq_eq_sub_eq_zero _ _ a₁, @eq_eq_sub_eq_zero _ _ b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq [LinearOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : α} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, ge_iff_le, mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero _ _ b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq [LinearOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : α} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← mul_zero c, gt_iff_lt, mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero _ _ b₁, ← this hc₁, ← this hc₂, h]

open Lean

open Lean Mathlib.Tactic.RingNF in
/-- Use `arithPolyNormCore` to rewrite the main goal. -/
def arithPolyNormCore (mv : MVarId) : MetaM (Option MVarId) := mv.withContext do
  let tgt ← instantiateMVars (← mv.getType)
  let s ← IO.mkRef {}
  let r ← M.run s {} <| rewrite tgt
  if r.expr.consumeMData.isConstOf ``True then
    mv.assign (← Meta.mkOfEqTrue (← r.getProof))
    return none
  else
    Meta.applySimpResultToTarget mv tgt r

def traceArithPolyNorm (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

/-- Use `arithPolyNorm` to rewrite the main goal. -/
def arithPolyNorm (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.arithPolyNorm traceArithPolyNorm do
  mv.withContext do
  if let .some mv ← arithPolyNormCore mv then
    throwError "[arithPolyNorm]: could not prove {← mv.getType}"

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  if let some (_, mv) ← normNumAt mv default #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

open Qq in
partial def findConst (α : Q(Type)) (hα : Q(LinearOrderedRing $α)) (e : Q($α)) : MetaM Expr := do
  match e with
  | ~q($a * $b) => findConst α hα b
  | ~q($a + $b) => findConst α hα b
  | ~q($a - $b) => findConst α hα b
  | ~q(-$a)     => findConst α hα a
  | _           =>
    if e.hasFVar || e.hasLooseBVars then
      return q(1 : $α)
    else if e.getUsedConstants.contains ``Neg.neg then
      let e : Q(Real) := e
      match e with
      | ~q((-$a) / $b) => return q($a / $b)
      | _              => return e
    else
      return e

end Smt.Arith
