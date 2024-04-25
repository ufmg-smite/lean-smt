/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Arith.ArithMulSign
import Smt.Reconstruct.Arith.MulPosNeg
import Smt.Reconstruct.Arith.Rewrites
import Smt.Reconstruct.Arith.SumBounds
import Smt.Reconstruct.Arith.Rewrites
import Smt.Reconstruct.Arith.TangentPlane
import Smt.Reconstruct.Arith.TightBounds
import Smt.Reconstruct.Arith.Trichotomy
import Smt.Reconstruct

namespace Smt.Reconstruct.Arith

open Lean hiding Rat
open Qq

@[smt_sort_reconstruct] def reconstructArithSort : SortReconstructor := fun s => do match s.getKind with
  | .INTEGER_SORT => return q(Int)
  | .REAL_SORT    => return q(Real)
  | _             => return none

def getTypeAndInst (s : cvc5.Sort) : Σ α : Q(Type), Q(LinearOrderedRing $α) := match s.isInteger with
  | false => ⟨q(Real), q(Real.instLinearOrderedRingReal)⟩
  | true  => ⟨q(Int), q(Int.linearOrderedCommRing.toLinearOrderedRing)⟩

def getTypeAndInst' (s : cvc5.Sort) : Σ (α : Q(Type)) (_ : Q(LinearOrderedRing $α)), Q(FloorRing $α) := match s.isInteger with
  | false => ⟨q(Real), q(Real.instLinearOrderedRingReal), q(Real.instFloorRingRealInstLinearOrderedRingReal)⟩
  | true  => ⟨q(Int), q(Int.linearOrderedCommRing.toLinearOrderedRing), q(instFloorRingIntToLinearOrderedRingLinearOrderedCommRing)⟩

@[smt_term_reconstruct] def reconstructArith : TermReconstructor := fun t => do match t.getKind with
  | .SKOLEM => match t.getSkolemId with
    | .DIV_BY_ZERO => return q(fun (x : Real) => x / 0)
    | .INT_DIV_BY_ZERO => return q(fun (x : Int) => x / 0)
    | .MOD_BY_ZERO => return q(fun (x : Int) => x % 0)
    -- | .SQRT => return q(Real.sqrt)
    | _ => return none
  | .CONST_INTEGER =>
    let x : Int := t.getIntegerValue
    let x' : Q(Nat) := mkRawNatLit x.natAbs
    if x ≥ 0 then
      return q(OfNat.ofNat $x' : Int)
    else
      return q(-(OfNat.ofNat $x' : Int))
  | .CONST_RATIONAL =>
    let x := t.getRationalValue
    let num : Q(Real) := mkRealLit x.num.natAbs
    if x.den == 1 then
      if x.num ≥ 0 then
        return q($num)
      else
        return q(-$num)
    else
      let den : Q(Real) := mkRealLit x.den
      if x.num ≥ 0 then
        return q($num / $den)
      else
        return q(-$num / $den)
  | .NEG =>
    let ⟨α, _⟩ := getTypeAndInst t.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    let ⟨α, _⟩ := getTypeAndInst t.getSort
    leftAssocOp q(@HSub.hSub $α $α $α _) t
  | .ADD =>
    let ⟨α, _⟩ := getTypeAndInst t.getSort
    leftAssocOp q(@HAdd.hAdd $α $α $α _) t
  | .MULT =>
    let ⟨α, _⟩ := getTypeAndInst t.getSort
    leftAssocOp q(@HMul.hMul $α $α $α _) t
  | .INTS_DIVISION =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .INTS_DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .DIVISION =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .INTS_MODULUS =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .INTS_MODULUS_TOTAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .ABS =>
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(Int.natAbs $x : Int)
  | .LEQ =>
    let ⟨α, _⟩ := getTypeAndInst t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .LT =>
    let ⟨α, _⟩ := getTypeAndInst t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x < $y)
  | .GEQ =>
    let ⟨α, _⟩ := getTypeAndInst t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .GT =>
    let ⟨α, _⟩ := getTypeAndInst t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x > $y)
  | .TO_REAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    return q($x : Real)
  | .TO_INTEGER =>
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(⌊$x⌋)
  | .IS_INTEGER =>
    let x : Q(Real) ← reconstructTerm t[0]!
    return q($x = ⌊$x⌋)
  | _ => return none
where
  mkRealLit (n : Nat) : Q(Real) := match h : n with
    | 0     => q(0 : Real)
    | 1     => q(1 : Real)
    | _ + 2 =>
      let h : Q(Nat.AtLeastTwo $n) := h ▸ q(instNatAtLeastTwo)
      let h := mkApp3 q(@instOfNatAtLeastTwo Real) (mkRawNatLit n) q(Real.natCast) h
      mkApp2 q(@OfNat.ofNat Real) (mkRawNatLit n) h
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | _ => return none
@[smt_proof_reconstruct] def reconstructArithProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | _ => return none

end Smt.Reconstruct.Arith
