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
  | .SKOLEM => match t.getSkolemId! with
    | .INT_DIV_BY_ZERO => return q(fun (x : Int) => x / 0)
    | .MOD_BY_ZERO => return q(fun (x : Int) => x % 0)
    | _ => return none
  | .CONST_INTEGER =>
    let x : Int := t.getIntegerValue!
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
  | .ARITH_POW_ELIM =>
    if !pf.getResult[0]![0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
    let c : Q(Nat) ← reconstructTerm pf.getResult[0]![1]!
    let y : Q(Int) ← reconstructTerm pf.getResult[1]!
    addThm q($x ^ $c = $y) q(Eq.refl ($x ^ $c))
  | .ARITH_INT_DIV_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t / $s = $t / $s) q(@Rewrite.div_total $t $s $h)
  | .ARITH_INT_DIV_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 1 = $t) q(@Rewrite.div_total_one $t)
  | .ARITH_INT_DIV_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t / 0 = 0) q(@Rewrite.div_total_zero $t)
  | .ARITH_INT_DIV_TOTAL_NEG =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q($t / $s = -($t / -$s)) q(@Rewrite.div_total_neg $t $s)
  | .ARITH_INT_MOD_TOTAL =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t % $s = $t % $s) q(@Rewrite.mod_total $t $s $h)
  | .ARITH_INT_MOD_TOTAL_ONE =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 1 = 0) q(@Rewrite.mod_total_one $t)
  | .ARITH_INT_MOD_TOTAL_ZERO =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q($t % 0 = $t) q(@Rewrite.mod_total_zero $t)
  | .ARITH_INT_MOD_TOTAL_NEG =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q($t % $s = $t % -$s) q(@Rewrite.mod_total_neg $t $s)
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
  | .ARITH_ELIM_INT_GT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t > $s) = ($t ≥ $s + 1)) q(@Rewrite.elim_gt_add_one $t $s)
  | .ARITH_ELIM_INT_LT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t < $s) = ($s ≥ $t + 1)) q(@Rewrite.elim_lt_add_one $t $s)
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
  | .ARITH_GEQ_NORM1_INT =>
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
  | .ARITH_EQ_ELIM_INT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t = $s) = ($t ≥ $s ∧ $t ≤ $s)) q(@Rewrite.eq_elim $t $s)
  | .ARITH_PLUS_FLATTEN =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let xs : Q(List Int) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Int) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Int) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(Int.addN ($xs ++ ([Int.addN ($w :: $ys)] ++ $zs)) = Int.addN ($xs ++ ($w :: $ys ++ $zs))) q(@Rewrite.plus_flatten $xs $w $ys $zs)
  | .ARITH_MULT_FLATTEN =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let xs : Q(List Int) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Int) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Int) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(Int.mulN ($xs ++ ([Int.mulN ($w :: $ys)] ++ $zs)) = Int.mulN ($xs ++ ($w :: $ys ++ $zs))) q(@Rewrite.mult_flatten $xs $w $ys $zs)
  | .ARITH_ABS_ELIM_INT =>
    let x : Q(Int) ← reconstructTerm pf.getArguments[1]!
    addThm q(«$x».abs = ite ($x < 0) (-$x) $x) q(@Rewrite.abs_elim $x)
  | .ARITH_MOD_OVER_MOD =>
    let c : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let ts : Q(List Int) ← reconstructTerms pf.getArguments[2]!.getChildren
    let r : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let ss : Q(List Int) ← reconstructTerms pf.getArguments[4]!.getChildren
    let h : Q($c ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q(Int.addN ($ts ++ ([$r % $c] ++ $ss)) % $c = Int.addN ($ts ++ ([$r] ++ $ss)) % $c) q(@Rewrite.mod_over_mod $c $ts $r $ss $h)
  | .ARITH_DIVISIBLE_ELIM =>
    let n : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let h : Q($n ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q(($n ∣ $t) = ($t % $n = 0)) q(@Rewrite.divisible_elim $n $t $h)
  | .ARITH_ABS_EQ =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((«$x».abs = «$y».abs) = ($x = $y ∨ $x = -$y)) q(@Rewrite.abs_eq $x $y)
  | .ARITH_ABS_INT_GT =>
    let x : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((«$x».abs > «$y».abs) = ite ($x ≥ 0) (ite ($y ≥ 0) ($x > $y) ($x > -$y)) (ite ($y ≥ 0) (-$x > $y) (-$x > -$y)))
           q(@Rewrite.abs_gt $x $y)
  | .ARITH_GEQ_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s ≥ $r) = ite $c ($t ≥ $r) ($s ≥ $r)) q(@Rewrite.geq_ite_lift $c $hc $t $s $r)
  | .ARITH_GT_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s > $r) = ite $c ($t > $r) ($s > $r)) q(@Rewrite.gt_ite_lift $c $hc $t $s $r)
  | .ARITH_LEQ_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s ≤ $r) = ite $c ($t ≤ $r) ($s ≤ $r)) q(@Rewrite.leq_ite_lift $c $hc $t $s $r)
  | .ARITH_LT_ITE_LIFT =>
    if !pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Int) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Int) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s < $r) = ite $c ($t < $r) ($s < $r)) q(@Rewrite.lt_ite_lift $c $hc $t $s $r)
  | .ARITH_MIN_LT1 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t < $s) $t $s ≤ $t) = True) q(@Rewrite.min_lt1 $t $s)
  | .ARITH_MIN_LT2 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t < $s) $t $s ≤ $s) = True) q(@Rewrite.min_lt2 $t $s)
  | .ARITH_MAX_GEQ1 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t ≥ $s) $t $s ≥ $t) = True) q(@Rewrite.max_geq1 $t $s)
  | .ARITH_MAX_GEQ2 =>
    if !pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Int) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t ≥ $s) $t $s ≥ $s) = True) q(@Rewrite.max_geq2 $t $s)
  | _ => return none
where
  reconstructArgs (args : Array cvc5.Term) : ReconstructM (Array (Array Expr)) := do
    let mut args' := #[]
    for arg in args do
      let mut arg' := #[]
      if arg.getKind == .SEXPR then
        for subarg in arg do
          arg' := arg'.push (← reconstructTerm subarg)
      else
        arg' := arg'.push (← reconstructTerm arg)
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
      throwError "[sum_ub]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind
  let ls : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addThm (if ks == .LT then q($ls < $rs) else q($ls ≤ $rs)) hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := pf.getResult[0]!.getChildren
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : Std.HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]
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
    let h : Q($q) ← if ts[map[vs[0]!]!]!.getKind == .NOT then
        let a : Q(Int) ← reconstructTerm vs[0]!
        let ha : Q($a ≠ 0) := hs[map[vs[0]!]!]!
        go vs ts hs map .GT q($a * $a) q(Int.mul_sign₀ $ha) 2
      else
        let a : Q(Int) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map[vs[0]!]!]!.getKind a hs[map[vs[0]!]!]! 1
    Meta.mkLambdaFVars hs h
  addThm q(andN $ps → $q) q(Builtin.scopes $h)
where
  go vs ts hs map (ka : cvc5.Kind) (a : Q(Int)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Int) ← reconstructTerm vs[i]
      let k : cvc5.Kind := ts[map[vs[i]]!]!.getKind
      if ka == .LT && k == .LT then
        let ha : Q($a < 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Int.mul_sign₁ $ha $hb) (i + 1)
      else if ka == .LT && k == .NOT then
        let ha : Q($a < 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b * $b) q(Int.mul_sign₂ $ha $hb) (i + 2)
      else if ka == .LT && k == .GT then
        let ha : Q($a < 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Int.mul_sign₃ $ha $hb) (i + 1)
      else if ka == .GT && k == .LT then
        let ha : Q($a > 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Int.mul_sign₄ $ha $hb) (i + 1)
      else if ka == .GT && k == .NOT then
        let ha : Q($a > 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b * $b) q(Int.mul_sign₅ $ha $hb) (i + 2)
      else if ka == .GT && k == .GT then
        let ha : Q($a > 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Int.mul_sign₆ $ha $hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let cx : Int := pf.getChildren[0]!.getResult[0]![0]!.getIntegerValue!
  let cy : Int := pf.getChildren[0]!.getResult[1]![0]!.getIntegerValue!
  let x₁ : Q(Int) ← reconstructTerm pf.getResult[0]![0]!
  let x₂ : Q(Int) ← reconstructTerm pf.getResult[0]![1]!
  let y₁ : Q(Int) ← reconstructTerm pf.getResult[1]![0]!
  let y₂ : Q(Int) ← reconstructTerm pf.getResult[1]![1]!
  let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructProof pf.getChildren[0]!
  let k := pf.getResult[0]!.getKind
  let (hcx, hcy) :=
    if k == .EQUAL then (q(@of_decide_eq_true ($cx ≠ 0) _), q(@of_decide_eq_true ($cy ≠ 0) _))
    else if cx > 0 then (q(@of_decide_eq_true ($cx > 0) _), q(@of_decide_eq_true ($cy > 0) _))
    else (q(@of_decide_eq_true ($cx < 0) _), q(@of_decide_eq_true ($cy < 0) _))
  let hcx := .app hcx q(Eq.refl true)
  let hcy := .app hcy q(Eq.refl true)
  let n ← getThmName k (cx > 0)
  return mkApp9 (.const n []) x₁ x₂ y₁ y₂ q($cx) q($cy) hcx hcy h
where
  getThmName (k : cvc5.Kind) (sign : Bool) : ReconstructM Name :=
    if k == .LT && sign == true then pure ``Int.lt_of_sub_eq_pos
    else if k == .LT && sign == false then pure ``Int.lt_of_sub_eq_neg
    else if k == .LEQ && sign == true then pure ``Int.le_of_sub_eq_pos
    else if k == .LEQ && sign == false then pure ``Int.le_of_sub_eq_neg
    else if k == .EQUAL then pure ``Int.eq_of_sub_eq
    else if k == .GEQ && sign == true then pure ``Int.ge_of_sub_eq_pos
    else if k == .GEQ && sign == false then pure ``Int.ge_of_sub_eq_neg
    else if k == .GT && sign == true then pure ``Int.gt_of_sub_eq_pos
    else if k == .GT && sign == false then pure ``Int.gt_of_sub_eq_neg
    else throwError "[arith_poly_norm_rel]: invalid combination of kind and sign: {k}, {sign}"

@[smt_proof_reconstruct] def reconstructIntProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    reconstructSumUB pf
  | .INT_TIGHT_UB =>
    if !pf.getChildren[0]!.getResult[1]!.getSort.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i < $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≤ $c - 1) q(@Int.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    if !pf.getChildren[0]!.getResult[1]!.getSort.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i > $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≥ $c + 1) q(@Int.int_tight_lb $c $i $h)
  | .ARITH_TRICHOTOMY =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    let x : Q(Int) ← reconstructTerm pf.getResult[0]!
    let c : Q(Int) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind
    let k₂ := pf.getChildren[1]!.getResult.getKind
    if k₁ == .LEQ && k₂ == .NOT then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Int.trichotomy₁ $h₁ $h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Int.trichotomy₂ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .LEQ then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Int.trichotomy₃ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Int.trichotomy₄ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Int.trichotomy₅ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .NOT then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Int.trichotomy₆ $h₁ $h₂)
    else
      return none
  | .ARITH_POLY_NORM =>
    if !pf.getResult[0]!.getSort.isInteger then return none
    let a : Q(Int) ← reconstructTerm pf.getResult[0]!
    let b : Q(Int) ← reconstructTerm pf.getResult[1]!
    addTac q($a = $b) Int.polyNorm
  | .ARITH_POLY_NORM_REL =>
    if !pf.getChildren[0]!.getResult[0]![0]!.getSort.isInteger then return none
    reconstructArithPolyNormRel pf
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
