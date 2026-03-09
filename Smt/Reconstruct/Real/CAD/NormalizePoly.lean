import Mathlib
import Lean

theorem not_lt_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a < b) → a ≥ b := not_lt.mp
theorem not_le_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a ≤ b) → a > b := not_le.mp

open Qq Lean Elab Tactic Meta

syntax (name := simple_push_neg) "simple_push_neg" term : tactic

def apply_not (h : Expr) : MetaM Expr := do
  let t ← inferType h
  match t with
  | .app (.const `Not ..) e =>
    match e with
    | .app (.app (.app (.app (.const `LT.lt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `LE.le ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | .app (.app (.app (.app (.const `GT.gt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | (.app (.app (.app (.const ``Eq ..) _) _) _) => return h -- hmm
    | _ =>
      logInfo m!"e = {repr e}"
      throwError "[simple_push_neg]: impossible"
  | _ => return h

@[tactic simple_push_neg] def evalSimplePushNeg : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← apply_not h
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

@[tactic normalize_rel] def evalNormalizeRel : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  sorry

#check whnfR

example (a : Real) : 31 * a + 45 * a^2 + 2 * a * a - 1 = 47 * a ^ 2 + 31 * a - 1 := by ring
example (a : Real) : a + 2 * a * a - a = 2 * a ^ 2 := by ring
