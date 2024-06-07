/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Arith.ArithMulSign
import Smt.Reconstruct.Arith.ArithPolyNorm
import Smt.Reconstruct.Arith.MulPosNeg
import Smt.Reconstruct.Arith.Rewrites
import Smt.Reconstruct.Arith.SumBounds
import Smt.Reconstruct.Arith.Rewrites
import Smt.Reconstruct.Arith.TangentPlane
import Smt.Reconstruct.Arith.TightBounds
import Smt.Reconstruct.Arith.Trichotomy
import Smt.Reconstruct.Rewrite

namespace Smt.Reconstruct.Arith

open Lean
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
  | .ARITH_DIV_BY_CONST_ELIM =>
    let t : Q(Real) ← reconstructTerm pf.getResult[0]![0]!
    let r := pf.getResult[0]![1]!.getRationalValue
    if r.den == 1 then
      let c : Q(Real) := reconstructArith.mkRealLit r.num.natAbs
      if r.num ≥ 0 then
        if r.num == 1 then
          addThm q($t / 1 = $t * 1) q(@Arith.arith_div_by_const_elim_1_pos $t)
        else
          addThm q($t / $c = $t * (1 / $c)) q(@Arith.arith_div_by_const_elim_num_pos $t $c)
      else
        if r.num == -1 then
          addThm q($t / -1 = $t * -1) q(@Arith.arith_div_by_const_elim_1_neg $t)
        else
          addThm q($t / -$c = $t * (-1 / $c)) q(@Arith.arith_div_by_const_elim_num_neg $t $c)
    else
      let c₁ : Q(Real) := reconstructArith.mkRealLit r.num.natAbs
      let c₂ : Q(Real) := reconstructArith.mkRealLit r.den
      if r.num ≥ 0 then
        addThm q($t / ($c₁ / $c₂) = $t * ($c₂ / $c₁)) q(@Arith.arith_div_by_const_elim_real_pos $t $c₁ $c₂)
      else
        addThm q($t / (-$c₁ / $c₂) = $t * (-$c₂ / $c₁)) q(@Arith.arith_div_by_const_elim_real_neg $t $c₁ $c₂)
  | .ARITH_PLUS_ZERO =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]![0]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc $α _) q(@add_zero $α _) q(@Arith.arith_plus_zero $α $h) args)
  | .ARITH_MUL_ONE =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]![0]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc $α _) q(@mul_one $α _) q(@Arith.arith_mul_one $α $h) args)
  | .ARITH_MUL_ZERO =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]![0]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc $α _) q(@mul_one $α _) q(@Arith.arith_mul_zero $α $h) args)
  | .ARITH_DIV_TOTAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t / $s = $t / $s) q(@Arith.arith_div_total $t $s $h)
  | .ARITH_INT_DIV_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t / $s = $t / $s) q(@Arith.arith_int_div_total $t $s $h)
  | .ARITH_INT_DIV_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 1 = $t) q(@Arith.arith_int_div_total_one $t)
  | .ARITH_INT_DIV_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 0 = 0) q(@Arith.arith_int_div_total_zero $t)
  | .ARITH_INT_MOD_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t % $s = $t % $s) q(@Arith.arith_int_mod_total $t $s $h)
  | .ARITH_INT_MOD_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 1 = 0) q(@Arith.arith_int_mod_total_one $t)
  | .ARITH_INT_MOD_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 0 = $t) q(@Arith.arith_int_mod_total_zero $t)
  | .ARITH_NEG_NEG_ONE =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(-1 * (-1 * $t) = $t) q(@Arith.arith_neg_neg_one $α $h $t)
  | .ARITH_ELIM_UMINUS =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(-$t = -1 * $t) q(@Arith.arith_elim_uminus $α $h $t)
  | .ARITH_ELIM_MINUS =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q($t - $s = $t + -1 * $s) q(@Arith.arith_elim_minus $α $h $t $s)
  | .ARITH_ELIM_GT =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t > $s) = ¬($t ≤ $s)) q(@Arith.arith_elim_gt $α $h $t $s)
  | .ARITH_ELIM_LT =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t < $s) = ¬($t ≥ $s)) q(@Arith.arith_elim_lt $α $h $t $s)
  | .ARITH_ELIM_LEQ =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≤ $s) = ($s ≥ $t)) q(@Arith.arith_elim_leq $α $h $t $s)
  | .ARITH_LEQ_NORM =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≤ $s) = ¬($t ≥ $s + 1)) q(@Arith.arith_leq_norm $t $s)
  | .ARITH_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬($t ≥ $s)) = ($s ≥ $t + 1)) q(@Arith.arith_geq_tighten $t $s)
  | .ARITH_GEQ_NORM1 =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = ($t - $s ≥ 0)) q(@Arith.arith_geq_norm1 $α $h $t $s)
  | .ARITH_GEQ_NORM2 =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = (-$t ≤ -$s)) q(@Arith.arith_geq_norm2 $α $h $t $s)
  | .ARITH_REFL_LEQ =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≤ $t) = True) q(@Arith.arith_refl_leq $α $h $t)
  | .ARITH_REFL_LT =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t < $t) = False) q(@Arith.arith_refl_lt $α $h $t)
  | .ARITH_REFL_GEQ =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≥ $t) = True) q(@Arith.arith_refl_geq $α $h $t)
  | .ARITH_REFL_GT =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t > $t) = False) q(@Arith.arith_refl_gt $α $h $t)
  | .ARITH_PLUS_FLATTEN =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[2]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc $α _) q(@add_zero $α _) q(@Arith.arith_plus_flatten $α $h) args)
  | .ARITH_MULT_FLATTEN =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[2]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc $α _) q(@mul_one $α _) q(@Arith.arith_mult_flatten $α $h) args)
  | .ARITH_MULT_DIST =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc $α _) q(@mul_one $α _) q(@Arith.arith_mult_dist $α $h) args)
  | .ARITH_PLUS_CANCEL1 =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[2]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc $α _) q(@add_zero $α _) q(@Arith.arith_plus_cancel1 $α $h) args)
  | .ARITH_PLUS_CANCEL2 =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[2]!.getSort
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc $α _) q(@add_zero $α _) q(@Arith.arith_plus_cancel2 $α $h) args)
  | .ARITH_ABS_ELIM =>
    let ⟨α, h⟩ := getTypeAndInst pf.getArguments[1]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(|$x| = if $x < 0 then -$x else $x) q(@Arith.arith_abs_elim $α $h $x)
  | _ => return none
where
  reconstructArgs (args : Array cvc5.Term) : ReconstructM (Array (Array Expr)) := do
    let mut args' := #[]
    for arg in args do
      let mut arg' := #[]
      for subarg in arg do
        arg' := arg'.push (← reconstructTerm subarg)
      args' := args'.push arg'
    return args'

@[smt_proof_reconstruct] def reconstructArithProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .EVALUATE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    let h : Q(Decidable ($t = $t')) ← Meta.synthInstance q(Decidable ($t = $t'))
    if !(h.getUsedConstants.any (isNoncomputable (← getEnv))) then
      return none
    addTac q($t = $t') Arith.normNum
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    addTac (← reconstructTerm pf.getResult) (Arith.sumBounds · (← pf.getChildren.mapM reconstructProof))
  | .INT_TIGHT_UB =>
    let ⟨α, h₁, h₂⟩ := getTypeAndInst' pf.getChildren[0]!.getResult[1]!.getSort
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q($α) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i < $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≤ ⌈$c⌉ - 1) q(@Arith.intTightUb' $α $h₁ $h₂ $i $c $h)
  | .INT_TIGHT_LB =>
    let ⟨α, h₁, h₂⟩ := getTypeAndInst' pf.getChildren[0]!.getResult[1]!.getSort
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q($α) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i > $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≥ ⌊$c⌋ + 1) q(@Arith.intTightLb' $α $h₁ $h₂ $i $c $h)
  | .ARITH_TRICHOTOMY =>
    let ⟨α, _⟩ := getTypeAndInst pf.getResult[0]!.getSort
    let x : Q($α) ← reconstructTerm pf.getResult[0]!
    let c : Q($α) ← reconstructTerm pf.getResult[1]!
    match pf.getChildren[0]!.getResult.getKind, pf.getChildren[1]!.getResult.getKind with
    | .GEQ, .NOT =>
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Arith.trichotomy₁ (not_lt_of_ge $h₁) $h₂)
    | .NOT, .GEQ =>
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Arith.trichotomy₂ $h₁ (not_lt_of_ge $h₂))
    | .GEQ, .LEQ =>
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Arith.trichotomy₃ (not_lt_of_ge $h₁) (Arith.not_gt_of_le $h₂))
    | .LEQ, .GEQ =>
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Arith.trichotomy₄ (Arith.not_gt_of_le $h₁) (not_lt_of_ge $h₂))
    | .NOT, .LEQ =>
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Arith.trichotomy₅ $h₁ (Arith.not_gt_of_le $h₂))
    | .LEQ, .NOT =>
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Arith.trichotomy₆ (Arith.not_gt_of_le $h₁) $h₂)
    | _, _ => return none
  | .ARITH_POLY_NORM =>
    let k := pf.getResult[0]!.getSort.getKind
    if k == .REAL_SORT || k == .INTEGER_SORT then
      let ⟨α, _⟩ := getTypeAndInst pf.getResult[0]!.getSort
      let a : Q($α) ← reconstructTerm pf.getResult[0]!
      let b : Q($α) ← reconstructTerm pf.getResult[1]!
      addTac q($a = $b) Arith.arithPolyNorm
    else
      let ⟨α, hα⟩ := getTypeAndInst pf.getResult[0]![0]!.getSort
      let a₁ : Q($α) ← reconstructTerm pf.getResult[0]![0]!
      let a₂ : Q($α) ← reconstructTerm pf.getResult[0]![1]!
      let b₁ : Q($α) ← reconstructTerm pf.getResult[1]![0]!
      let b₂ : Q($α) ← reconstructTerm pf.getResult[1]![1]!
      -- ≠ is a hack to avoid closing the goal (if it's true)
      let h : Q($a₁ - $a₂ ≠ $b₁ - $b₂) ← Meta.mkFreshExprMVar q($a₁ - $a₂ ≠ $b₁ - $b₂)
      let some mv ← Arith.arithPolyNormCore h.mvarId! | return none
      let t ← mv.getType
      let c₁ : Q($α) ← Arith.findConst α hα t.appArg!
      let c₂ : Q($α) ← Arith.findConst α hα t.appFn!.appArg!
      let hc₁ : Q($c₁ > 0) ← Meta.mkFreshExprMVar q($c₁ > 0)
      let hc₂ : Q($c₂ > 0) ← Meta.mkFreshExprMVar q($c₂ > 0)
      Arith.normNum hc₁.mvarId!
      Arith.normNum hc₂.mvarId!
      let h : Q($c₁ * ($a₁ - $a₂) = $c₂ * ($b₁ - $b₂)) ← Meta.mkFreshExprMVar q($c₁ * ($a₁ - $a₂) = $c₂ * ($b₁ - $b₂))
      Arith.arithPolyNorm h.mvarId!
      match pf.getResult[0]!.getKind with
      | .LT =>
        addThm q(($a₁ < $a₂) = ($b₁ < $b₂)) q(Arith.lt_of_sub_eq $hc₁ $hc₂ $h)
      | .LEQ =>
        addThm q(($a₁ ≤ $a₂) = ($b₁ ≤ $b₂)) q(Arith.le_of_sub_eq $hc₁ $hc₂ $h)
      | .EQUAL =>
        addThm q(($a₁ = $a₂) = ($b₁ = $b₂)) q(Arith.eq_of_sub_eq $hc₁ $hc₂ $h)
      | .GEQ =>
        addThm q(($a₁ ≥ $a₂) = ($b₁ ≥ $b₂)) q(Arith.ge_of_sub_eq $hc₁ $hc₂ $h)
      | .GT =>
        addThm q(($a₁ > $a₂) = ($b₁ > $b₂)) q(Arith.gt_of_sub_eq $hc₁ $hc₂ $h)
      | _   => return none
  | .ARITH_MULT_SIGN =>
    let args := pf.getArguments
    let m := args.back
    let pol (k : cvc5.Kind) : Fin 3 := match k with
      | .LT    => 0
      | .EQUAL => 1
      | .GT    => 2
      | _      => panic! "[arithMulSign]: invalid polarity"
    let exp (t : cvc5.Term) : Nat := Id.run do
      let mut count := 0
      for t' in m do
        if t' == t then
          count := count + 1
      return count
    let mut es := #[]
    for i in [0:args.size - 1] do
      let arg := if args[i]!.getKind == .NOT then args[i]![0]! else args[i]!
      if arg[0]!.getKind == .CONST_INTEGER || arg[0]!.getKind == .CONST_RATIONAL then
        es := es.push (← reconstructTerm arg[1]!, 2 - pol arg.getKind, exp arg[1]!)
      else
        es := es.push (← reconstructTerm arg[0]!, pol arg.getKind, exp arg[0]!)
    addTac (← reconstructTerm pf.getResult) (Arith.mulSign · es)
  | .ARITH_MULT_POS =>
    let ⟨α, _⟩ := getTypeAndInst pf.getArguments[0]!.getSort
    let m : Q($α) ← reconstructTerm pf.getArguments[0]!
    let l : Q($α) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q($α) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m > 0 ∧ $l < $r → $m * $l < $m * $r) q(@Arith.arith_mul_pos_lt _ _ $l $r $m)
    | .LEQ =>
      addThm q($m > 0 ∧ $l ≤ $r → $m * $l ≤ $m * $r) q(@Arith.arith_mul_pos_le _ _ $l $r $m)
    | .EQUAL =>
      addThm q($m > 0 ∧ $l = $r → $m * $l = $m * $r) q(@Arith.arith_mul_pos_eq _ _ $l $r $m)
    | .GEQ =>
      addThm q($m > 0 ∧ $l ≥ $r → $m * $l ≥ $m * $r) q(@Arith.arith_mul_pos_ge _ _ $l $r $m)
    | .GT =>
      addThm q($m > 0 ∧ $l > $r → $m * $l > $m * $r) q(@Arith.arith_mul_pos_gt _ _ $l $r $m)
    | _ => return none
  | .ARITH_MULT_NEG =>
    let ⟨α, _⟩ := getTypeAndInst pf.getArguments[0]!.getSort
    let m : Q($α) ← reconstructTerm pf.getArguments[0]!
    let l : Q($α) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q($α) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m < 0 ∧ $l < $r → $m * $l > $m * $r) q(@Arith.arith_mul_neg_lt _ _ $l $r $m)
    | .LEQ =>
      addThm q($m < 0 ∧ $l ≤ $r → $m * $l ≥ $m * $r) q(@Arith.arith_mul_neg_le _ _ $l $r $m)
    | .EQUAL =>
      addThm q($m < 0 ∧ $l = $r → $m * $l = $m * $r) q(@Arith.arith_mul_neg_eq _ _ $l $r $m)
    | .GEQ =>
      addThm q($m < 0 ∧ $l ≥ $r → $m * $l ≤ $m * $r) q(@Arith.arith_mul_neg_ge _ _ $l $r $m)
    | .GT =>
      addThm q($m < 0 ∧ $l > $r → $m * $l < $m * $r) q(@Arith.arith_mul_neg_gt _ _ $l $r $m)
    | _ => return none
  | .ARITH_MULT_TANGENT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let a : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let b : Q(Real) ← reconstructTerm pf.getArguments[3]!
    if pf.getArguments[4]!.getIntegerValue == -1 then
      addThm q(($x * $y ≤ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≥ $b ∨ $x ≥ $a ∧ $y ≤ $b)) q(Arith.arithMulTangentLowerEq $x $y $a $b)
    else
      addThm q(($x * $y ≥ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≤ $b ∨ $x ≥ $a ∧ $y ≥ $b)) q(Arith.arithMulTangentUpperEq $x $y $a $b)
  | _ => return none

end Smt.Reconstruct.Arith
