/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Smt.Reconstruct
import Mathlib.Data.Finset.Basic

private def Std.Range.foldlM [Monad m] (f : α → Nat → m α) (r : Range) (init : α) : m α := do
  let mut a := init
  for i in r do
    a ← f a i
  return a

namespace Smt.Reconstruct.ZMod

open Lean Qq


-- @[smt_sort_reconstruct] def reconstructSetSort : SortReconstructor := fun s => do match s.getKind with
--   | .SET_SORT=>
--     let u ← Meta.getLevel (← reconstructSort s.getSetElementSort!)
--     let α : Q(Type u) ← reconstructSort s.getSetElementSort!
--     return q(Finset $α)
--   | _             => return none

--   @[smt_term_reconstruct] def reconstructSetOp : TermReconstructor := fun t => do match t.getKind with
--   | .SET_IS_EMPTY =>
--     let u ← Meta.getLevel (← reconstructSort t.getChildren[0]!.getSort)
--     let α : Q(Type u) ← reconstructSort t.getChildren[0]!.getSort
--     let s : Q(Finset $α) ← reconstructTerm t.getChildren[0]!
--     return q($s = ∅)
--   | _ => return none
-- where
--   leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
--     let mut curr ← reconstructTerm t[0]!
--     for i in [1:t.getNumChildren] do
--       curr := mkApp2 op curr (← reconstructTerm t[i]!)
--     return curr
