/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Smt.Reconstruct
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic

private def Std.Range.foldlM [Monad m] (f : α → Nat → m α) (r : Range) (init : α) : m α := do
  let mut a := init
  for i in r do
    a ← f a i
  return a

namespace Smt.Reconstruct.ZMod

open Lean Qq


universe u

--variable {n : ℕ} [Fact n.Prime]
--variable {σ : Type u}

abbrev R (n : ℕ) := ZMod n
abbrev P (n : ℕ) (σ : Type u) := MvPolynomial σ (R n)

/-- Expressions over variables `σ` with coefficients in `ZMod n`. -/
inductive ZModExpr (n : ℕ) (σ : Type u) : Type u
| var   : σ → ZModExpr n σ
| const : R n → ZModExpr n σ
| add   : ZModExpr n σ → ZModExpr n σ → ZModExpr n σ
| mul   : ZModExpr n σ → ZModExpr n σ → ZModExpr n σ
| neg   : ZModExpr n σ → ZModExpr n σ
| pow   : ZModExpr n σ → ℕ → ZModExpr n σ

namespace ZModExpr

noncomputable section

def toPoly {n : ℕ} {σ : Type u} : ZModExpr n σ → P n σ
| .var i     => MvPolynomial.X i
| .const c   => MvPolynomial.C c
| .add a b   => toPoly a + toPoly b
| .mul a b   => toPoly a * toPoly b
| .neg a     =>  MvPolynomial.C (-1) * toPoly a
| .pow a k   => (toPoly a) ^ k


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
  -- | .FINITE_FIELD_VARIETY => sorry
  -- | .FINITE_FIELD_IDEAL => sorry
  --   let w : Nat := t.getSort.getFiniteFieldSize!
  --   leftAssocOp q(@HMul.hMul (ZMod $w) (ZMod $w) (ZMod $w) _) t

  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr
