/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas

import Mathlib.Algebra.Order.Floor
import Lean

open Lean hiding Rat
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying.Arith.TightBounds.Tactic

open Lemmas

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
  | app (app (app (app _ (const ``Int ..)) ..) ..) .. => True
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
  | app (app (app (app _ (const ``Int ..)) ..) ..) .. => True
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

end Smt.Reconstruction.Certifying.Arith.TightBounds.Tactic
