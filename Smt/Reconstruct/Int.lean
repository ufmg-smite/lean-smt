/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Builtin.Lemmas
import Smt.Reconstruct.Int.Core
import Smt.Reconstruct.Int.Lemmas
import Smt.Reconstruct.Int.Polynorm
import Smt.Reconstruct.Int.Rewrites
import Smt.Reconstruct.Rewrite

namespace Smt.Reconstruct.Int

open Lean
open Qq

@[smt_sort_reconstruct] def reconstructIntSort : SortReconstructor := fun s => do match s.getKind with
  | .INTEGER_SORT => return q(Int)
  | _             => return none

@[smt_term_reconstruct] def reconstructInt : TermReconstructor := fun t => do match t.getKind with
  | .SKOLEM => match t.getSkolemId with
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
  | .NEG =>
    if !t.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    if !t.getSort.isInteger then return none
    leftAssocOp q(@HSub.hSub Int Int Int _) t
  | .ADD =>
    if !t.getSort.isInteger then return none
    leftAssocOp q(@HAdd.hAdd Int Int Int _) t
  | .MULT =>
    if !t.getSort.isInteger then return none
    leftAssocOp q(@HMul.hMul Int Int Int _) t
  | .INTS_DIVISION =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .INTS_DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Int Int Int _) t
  | .INTS_MODULUS =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .INTS_MODULUS_TOTAL =>
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x % $y)
  | .ABS =>
    if !t.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(if $x < 0 then -$x else $x)
  | .LEQ =>
    if !t[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .LT =>
    if !t[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x < $y)
  | .GEQ =>
    if !t[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .GT =>
    if !t[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm t[0]!
    let y : Q(Int) ← reconstructTerm t[1]!
    return q($x > $y)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | .ARITH_PLUS_ZERO =>
    if !pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.add_assoc) q(Int.add_zero) q(@Rewrite.plus_zero) args)
  | .ARITH_MUL_ONE =>
    if !pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.mul_assoc) q(Int.mul_one) q(@Rewrite.mul_one) args)
  | .ARITH_MUL_ZERO =>
    if !pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.mul_assoc) q(Int.mul_one) q(@Rewrite.mul_zero) args)
  | .ARITH_INT_DIV_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t / $s = $t / $s) q(@Rewrite.int_div_total $t $s $h)
  | .ARITH_INT_DIV_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 1 = $t) q(@Rewrite.int_div_total_one $t)
  | .ARITH_INT_DIV_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 0 = 0) q(@Rewrite.int_div_total_zero $t)
  | .ARITH_INT_MOD_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t % $s = $t % $s) q(@Rewrite.int_mod_total $t $s $h)
  | .ARITH_INT_MOD_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 1 = 0) q(@Rewrite.int_mod_total_one $t)
  | .ARITH_INT_MOD_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 0 = $t) q(@Rewrite.int_mod_total_zero $t)
  | .ARITH_NEG_NEG_ONE =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(-1 * (-1 * $t) = $t) q(@Rewrite.neg_neg_one $t)
  | .ARITH_ELIM_UMINUS =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(-$t = -1 * $t) q(@Rewrite.elim_uminus $t)
  | .ARITH_ELIM_MINUS =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q($t - $s = $t + -1 * $s) q(@Rewrite.elim_minus $t $s)
  | .ARITH_ELIM_GT =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t > $s) = ¬($t ≤ $s)) q(@Rewrite.elim_gt $t $s)
  | .ARITH_ELIM_LT =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t < $s) = ¬($t ≥ $s)) q(@Rewrite.elim_lt $t $s)
  -- | .ARITH_ELIM_INT_GT =>
  --   let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
  --   let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
  --   addThm q(($t > $s) = ($t ≥ $s + 1)) q(@Rewrite.elim_int_gt $t $s)
  -- | .ARITH_ELIM_INT_LT =>
  --   let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
  --   let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
  --   addThm q(($t < $s) = ($s ≥ $t + 1)) q(@Rewrite.elim_int_lt $t $s)
  | .ARITH_ELIM_LEQ =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≤ $s) = ($s ≥ $t)) q(@Rewrite.elim_leq $t $s)
  | .ARITH_LEQ_NORM =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≤ $s) = ¬($t ≥ $s + 1)) q(@Rewrite.leq_norm $t $s)
  | .ARITH_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬($t ≥ $s)) = ($s ≥ $t + 1)) q(@Rewrite.geq_tighten $t $s)
  | .ARITH_GEQ_NORM1 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = ($t - $s ≥ 0)) q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_GEQ_NORM2 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = (-$t ≤ -$s)) q(@Rewrite.geq_norm2 $t $s)
  | .ARITH_REFL_LEQ =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≤ $t) = True) q(@Rewrite.refl_leq $t)
  | .ARITH_REFL_LT =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t < $t) = False) q(@Rewrite.refl_lt $t)
  | .ARITH_REFL_GEQ =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≥ $t) = True) q(@Rewrite.refl_geq $t)
  | .ARITH_REFL_GT =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t > $t) = False) q(@Rewrite.refl_gt $t)
  | .ARITH_PLUS_FLATTEN =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.add_assoc) q(Int.add_zero) q(@Rewrite.plus_flatten) args)
  | .ARITH_MULT_FLATTEN =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.mul_assoc) q(Int.mul_one) q(@Rewrite.mult_flatten) args)
  | .ARITH_MULT_DIST =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.mul_assoc) q(Int.mul_one) q(@Rewrite.mult_dist) args)
  | .ARITH_PLUS_CANCEL1 =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.mul_assoc) q(Int.mul_one) q(@Rewrite.plus_cancel1) args)
  | .ARITH_PLUS_CANCEL2 =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(Int.add_assoc) q(Int.add_zero) q(@Rewrite.plus_cancel2) args)
  | .ARITH_ABS_ELIM =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(ite ($t < 0) (-$t) $t = ite ($t < 0) (-$t) $t) q(@Rewrite.abs_elim $t)
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

def reconstructSumUB (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let l : Q(Int) ← reconstructTerm p.getResult[0]!
    let r : Q(Int) ← reconstructTerm p.getResult[1]!
    let lsl := q($ls + $l)
    let rsr := q($rs + $r)
    let k := p.getResult.getKind
    if ks == .LT && k == .LT then
      let hs : Q($ls < $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₁ $hs $h))
    else if ks == .LT && k == .LEQ then
      let hs : Q($ls < $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₂ $hs $h))
    else if ks == .LT && k == .EQUAL then
      let hs : Q($ls < $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₃ $hs $h))
    else if ks == .LEQ && k == .LT then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₄ $hs $h))
    else if ks == .LEQ && k == .LEQ then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₅ $hs $h))
    else if ks == .LEQ && k == .EQUAL then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₆ $hs $h))
    else if ks == .EQUAL && k == .LT then
      let hs : Q($ls = $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Int.sum_ub₇ $hs $h))
    else if ks == .EQUAL && k == .LEQ then
      let hs : Q($ls = $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Int.sum_ub₈ $hs $h))
    else if ks == .EQUAL && k == .EQUAL then
      let hs : Q($ls = $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.EQUAL, lsl, rsr, q(Int.sum_ub₉ $hs $h))
    else
      throwError "[sum_ub]: invalid kinds: {ks}, {p.getResult.getKind}"
  let k := pf.getChildren[0]!.getResult.getKind
  let ls : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (_, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addThm q($ls < $rs) hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := pf.getResult[0]!.getChildren
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]'(h.right)
    let p : Q(Prop) ← reconstructTerm t
    hs := hs.push (Name.num `a i, fun _ => return p)
    map := map.insert (if t.getKind == .NOT then t[0]![0]! else t[0]!) i
  let t := pf.getResult[1]!
  let vs := if t[0]!.getKind == .CONST_INTEGER then t[1]!.getChildren else t[0]!.getChildren
  let f t ps := do
    let p : Q(Prop) ← reconstructTerm t
    return q($p :: $ps)
  let ps : Q(List Prop) ← ts.foldrM f q([])
  let q : Q(Prop) ← reconstructTerm t
  let h : Q(impliesN $ps $q) ← Meta.withLocalDeclsD hs fun hs => do
    let h : Q($q) ← if ts[map.find! vs[0]!]!.getKind == .NOT then
        let a : Q(Int) ← reconstructTerm vs[0]!
        let ha : Q($a ≠ 0) := hs[map.find! vs[0]!]!
        go vs ts hs map .GT q($a * $a) q(Int.mul_sign₀ $ha) 2
      else
        let a : Q(Int) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map.find! vs[0]!]!.getKind a hs[map.find! vs[0]!]! 1
    Meta.mkLambdaFVars hs h
  addThm q(andN $ps → $q) q(Builtin.scopes $h)
where
  go vs ts hs map ka (a : Q(Int)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Int) ← reconstructTerm vs[i]
      let k := ts[map.find! vs[i]]!.getKind
      if ka == .LT && k == .LT then
        let ha : Q($a < 0) := ha
        let hb : Q($b < 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b) q(Int.mul_sign₁ $ha $hb) (i + 1)
      else if ka == .LT && k == .NOT then
        let ha : Q($a < 0) := ha
        let hb : Q($b ≠ 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b * $b) q(Int.mul_sign₂ $ha $hb) (i + 2)
      else if ka == .LT && k == .GT then
        let ha : Q($a < 0) := ha
        let hb : Q($b > 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b) q(Int.mul_sign₃ $ha $hb) (i + 1)
      else if ka == .GT && k == .LT then
        let ha : Q($a > 0) := ha
        let hb : Q($b < 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b) q(Int.mul_sign₄ $ha $hb) (i + 1)
      else if ka == .GT && k == .NOT then
        let ha : Q($a > 0) := ha
        let hb : Q($b ≠ 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b * $b) q(Int.mul_sign₅ $ha $hb) (i + 2)
      else if ka == .GT && k == .GT then
        let ha : Q($a > 0) := ha
        let hb : Q($b > 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b) q(Int.mul_sign₆ $ha $hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

@[smt_proof_reconstruct] def reconstructIntProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    reconstructSumUB pf
  | .ARITH_TRICHOTOMY =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind
    let k₂ := pf.getChildren[1]!.getResult.getKind
    if k₁ == .GEQ && k₂ == .NOT then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Int.trichotomy₁ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Int.trichotomy₂ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Int.trichotomy₃ $h₁ $h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Int.trichotomy₄ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .LT then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Int.trichotomy₅ $h₁ $h₂)
    else if k₁ == .LT && k₂ == .NOT then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Int.trichotomy₆ $h₁ $h₂)
    else
      return none
  | .ARITH_POLY_NORM =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    let a : Q(Int) ← reconstructTerm pf.getResult[0]!
    let b : Q(Int) ← reconstructTerm pf.getResult[1]!
    addTac q($a = $b) Int.polyNorm
  | .ARITH_MULT_SIGN =>
    if !pf.getResult[1]![0]!.getSort.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if !pf.getArguments[0]!.getSort.isInteger then return none
    let m : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Int) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m > 0 ∧ $l < $r → $m * $l < $m * $r) q(@Int.mul_pos_lt $l $r $m)
    | .LEQ =>
      addThm q($m > 0 ∧ $l ≤ $r → $m * $l ≤ $m * $r) q(@Int.mul_pos_le $l $r $m)
    | .EQUAL =>
      addThm q($m > 0 ∧ $l = $r → $m * $l = $m * $r) q(@Int.mul_pos_eq $l $r $m)
    | .GEQ =>
      addThm q($m > 0 ∧ $l ≥ $r → $m * $l ≥ $m * $r) q(@Int.mul_pos_ge $l $r $m)
    | .GT =>
      addThm q($m > 0 ∧ $l > $r → $m * $l > $m * $r) q(@Int.mul_pos_gt $l $r $m)
    | _ => return none
  | .ARITH_MULT_NEG =>
    if !pf.getArguments[0]!.getSort.isInteger then return none
    let m : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Int) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m < 0 ∧ $l < $r → $m * $l > $m * $r) q(@Int.mul_neg_lt $l $r $m)
    | .LEQ =>
      addThm q($m < 0 ∧ $l ≤ $r → $m * $l ≥ $m * $r) q(@Int.mul_neg_le $l $r $m)
    | .EQUAL =>
      addThm q($m < 0 ∧ $l = $r → $m * $l = $m * $r) q(@Int.mul_neg_eq $l $r $m)
    | .GEQ =>
      addThm q($m < 0 ∧ $l ≥ $r → $m * $l ≤ $m * $r) q(@Int.mul_neg_ge $l $r $m)
    | .GT =>
      addThm q($m < 0 ∧ $l > $r → $m * $l < $m * $r) q(@Int.mul_neg_gt $l $r $m)
    | _ => return none
  | _ => return none

end Smt.Reconstruct.Int
