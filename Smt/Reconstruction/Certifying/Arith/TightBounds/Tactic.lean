import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas

import Mathlib.Algebra.Order.Floor
import Lean

open Lean Meta Elab.Tactic Expr

syntax (name := intTightUb) "intTightUb" term : tactic
@[tactic intTightUb] def evalIntTightUb : Tactic := fun stx =>
  withMainContext do
    let h ← elabTerm stx[1] none
    let t ← inferType h
    let hStx := ⟨stx[1]⟩
    if isIntLt t then
      evalTactic (← `(tactic| exact intTightUb' (castLT $hStx)))
    else
      evalTactic (← `(tactic| exact intTightUb' $hStx))
where
  isIntLt : Expr → Bool
  | app (app (app (app _ (const `Int ..)) ..) ..) .. => True
  | _ => False

syntax (name := intTightLb) "intTightLb" term : tactic
@[tactic intTightLb] def evalIntTightLb : Tactic := fun stx =>
  withMainContext do
    let h ← elabTerm stx[1] none
    let t ← inferType h
    let hStx := ⟨stx[1]⟩
    if isIntLt t then
      evalTactic (← `(tactic| exact intTightLb' (castLT $hStx)))
    else
      evalTactic (← `(tactic| exact intTightLb' $hStx))
where
  isIntLt : Expr → Bool
  | app (app (app (app _ (const `Int ..)) ..) ..) .. => True
  | _ => False

example {a b : Int} : a < b → (a : Int) ≤ Int.ceil (Rat.ofInt b) - 1 := by
  intro h
  intTightUb h

example {a : Int} : Rat.ofInt a < (7 : ℚ) → a ≤ Int.ceil (7 : Int) - 1 := by
  intro h
  intTightUb h

example {a b : Int} : a > b → (a : Int) ≥ Int.floor (Rat.ofInt b) + 1 := by
  intro h
  intTightLb h
