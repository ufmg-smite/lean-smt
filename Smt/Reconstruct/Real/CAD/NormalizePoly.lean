import Mathlib
import Lean
import CompPoly

import Smt.Reconstruct.Real.CAD.Utils

theorem not_lt_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a < b) → a ≥ b := not_lt.mp
theorem not_le_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a ≤ b) → a > b := not_le.mp

open Qq Lean Elab Tactic Meta

syntax (name := simple_push_neg) "simple_push_neg" term : tactic

def push_not (h : Expr) : MetaM Expr := do
  let t ← inferType h
  match t with
  | .app (.const `Not ..) e =>
    match e with
    | .app (.app (.app (.app (.const `LT.lt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `LE.le ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | .app (.app (.app (.app (.const `GT.gt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | .app (.app (.app (.const ``Eq ..) _) _) _ => return h -- hmm
    | _ =>
      throwError "[simple_push_neg]: impossible"
  | _ => return h

@[tactic simple_push_neg] def evalSimplePushNeg : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← push_not h
  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

example (a b : Real) : ¬ (32 * a - 4 < 45 * b^2 + b) → 32 * a -4 ≥ 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 ≤ 45 * b^2 + b) → 32 * a -4 > 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 > 45 * b^2 + b) → 32 * a -4 ≤ 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 ≥ 45 * b^2 + b) → 32 * a -4 < 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 = 45 * b^2 + b) → 32 * a -4 ≠ 45 * b ^ 2 + b := by
  intro h
  exact h

syntax (name := normalize_rel) "normalize_rel" term : tactic

lemma sub_neg_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightStrictMono α] {a b : α} : a < b → a - b < 0 := sub_neg.mpr
lemma tsub_nonpos_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightMono α] {a b : α} : a ≤ b → a - b ≤ 0 := tsub_nonpos.mpr
lemma sub_pos_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightStrictMono α] {a b : α} : a > b → a - b > 0 := sub_pos.mpr

def all_to_lhs (h : Expr) : MetaM Expr := do
  let t ← inferType h
  match t with
  | .app (.app (.app (.app (.const `LT.lt ..) _) _) _) _ => mkAppM ``sub_neg_mpr #[h]
  | .app (.app (.app (.app (.const `LE.le ..) _) _) _) _ => mkAppM ``tsub_nonpos_mpr #[h]
  | .app (.app (.app (.app (.const `GT.gt ..) _) _) _) _ => mkAppM ``sub_pos_mpr #[h]
  | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM ``sub_nonpos_of_le #[h]
  | .app (.app (.app (.const ``Eq ..) _) _) _ => mkAppM ``sub_eq_zero_of_eq #[h]
  | _ => throwError "[all_to_lhs]: impossible"

@[tactic normalize_rel] def evalNormalizeRel : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← all_to_lhs h
  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

example (a b : Rat) : (a ^ 2 + 3 * a - 24 = b * 23 + a) → True := by
  intro h
  normalize_rel h
  exact True.intro

open Mathlib.Tactic.RingNF in
def ring_compute_norm (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let rawResult ← Mathlib.Tactic.AtomM.recurse (← IO.mkRef {}) default (wellBehavedDischarge := true) evalExpr (cleanup default) e
  match rawResult.proof? with
  | none =>
    return none
  | some p =>
    return some ⟨rawResult.expr, p⟩

syntax (name := meta_norm) "meta_norm" term : tactic

def ring_normalize (h : Expr) : MetaM Expr := do
  let t ← inferType h
  let res ← ring_compute_norm t
  match res with
  | some ⟨_, eq_pf⟩ => rewriteWithEq h eq_pf
  | _ => return h

@[tactic meta_norm] def evalMetaNorm : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← ring_normalize h

  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]
