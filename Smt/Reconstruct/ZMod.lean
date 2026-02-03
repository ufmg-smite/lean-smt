/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Smt.Reconstruct
import Mathlib.Data.ZMod.Basic

private def Std.Range.foldlM [Monad m] (f : α → Nat → m α) (r : Range) (init : α) : m α := do
  let mut a := init
  for i in r do
    a ← f a i
  return a

namespace Smt.Reconstruct.ZMod

open Lean Qq


@[smt_sort_reconstruct] def reconstructZModSort : SortReconstructor := fun s => do match s.getKind with
  | .FINITE_FIELD_SORT =>
    let o : Nat := s.getFiniteFieldSize!
    return q(ZMod  $o)
  | _             => return none

  @[smt_term_reconstruct] def reconstructZMod : TermReconstructor := fun t => do match t.getKind with
  | .CONST_FINITE_FIELD =>
    let o : Nat := t.getSort.getFiniteFieldSize!
    if ho: o ≠  0 then
      let v : Fin o := @Fin.ofNat o ( NeZero.mk ho) (t.getFiniteFieldValue!.toInt! % o).toNat
      return q($v : ZMod $o)
    else
      throwError "Expected finite field order to be non zero but got {o}"
  | .FINITE_FIELD_ADD =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    leftAssocOp q(@HAdd.hAdd (ZMod $w) (ZMod $w) (ZMod $w) _) t
  | .FINITE_FIELD_MULT =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    leftAssocOp q(@HMul.hMul (ZMod $w) (ZMod $w) (ZMod $w) _) t
  | .FINITE_FIELD_NEG =>
    let w : Nat := t.getSort.getFiniteFieldSize!
    let x : Q(ZMod $w) ← reconstructTerm t[0]!
    return q(-$x)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr
