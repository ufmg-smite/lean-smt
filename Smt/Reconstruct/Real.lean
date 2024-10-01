/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Builtin.Lemmas
import Smt.Reconstruct.Real.Lemmas
import Smt.Reconstruct.Real.Polynorm
import Smt.Reconstruct.Real.Rewrites
import Smt.Reconstruct.Rewrite

namespace Smt.Reconstruct.Real

open Lean Qq

@[smt_sort_reconstruct] def reconstructRealSort : SortReconstructor := fun s => do match s.getKind with
  | .REAL_SORT => return q(Real)
  | _          => return none

@[smt_term_reconstruct] def reconstructReal : TermReconstructor := fun t => do match t.getKind with
  | .SKOLEM => match t.getSkolemId with
    | .DIV_BY_ZERO => return q(fun (x : Real) => x / 0)
    | _ => return none
  | .CONST_RATIONAL =>
    let c : Lean.Rat := t.getRationalValue
    let num : Q(Real) := mkRealLit c.num.natAbs
    if c.den == 1 then
      if c.num ≥ 0 then
        return q($num)
      else
        return q(-$num)
    else
      let den : Q(Real) := mkRealLit c.den
      if c.num ≥ 0 then
        return q($num / $den)
      else
        return q(-$num / $den)
  | .NEG =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(-$x)
  | .SUB =>
    if t.getSort.isInteger then return none
    leftAssocOp q(@HSub.hSub Real Real Real _) t
  | .ADD =>
    if t.getSort.isInteger then return none
    leftAssocOp q(@HAdd.hAdd Real Real Real _) t
  | .MULT =>
    if t.getSort.isInteger then return none
    leftAssocOp q(@HMul.hMul Real Real Real _) t
  | .DIVISION =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .DIVISION_TOTAL =>
    leftAssocOp q(@HDiv.hDiv Real Real Real _) t
  | .ABS =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(if $x < 0 then -$x else $x)
  | .LEQ =>
    if t[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .LT =>
    if t[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q($x < $y)
  | .GEQ =>
    if t[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .GT =>
    if t[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    let y : Q(Real) ← reconstructTerm t[1]!
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
      let h := mkApp3 q(@instOfNatAtLeastTwo Real) (mkRawNatLit n) q(Real.instNatCast) h
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
      let c : Q(Real) := reconstructReal.mkRealLit r.num.natAbs
      if r.num ≥ 0 then
        if r.num == 1 then
          addThm q($t / 1 = $t * 1) q(@Rewrite.div_by_const_elim_1_pos $t)
        else
          addThm q($t / $c = $t * (1 / $c)) q(@Rewrite.div_by_const_elim_num_pos $t $c)
      else
        if r.num == -1 then
          addThm q($t / -1 = $t * -1) q(@Rewrite.div_by_const_elim_1_neg $t)
        else
          addThm q($t / -$c = $t * (-1 / $c)) q(@Rewrite.div_by_const_elim_num_neg $t $c)
    else
      let c₁ : Q(Real) := reconstructReal.mkRealLit r.num.natAbs
      let c₂ : Q(Real) := reconstructReal.mkRealLit r.den
      if r.num ≥ 0 then
        addThm q($t / ($c₁ / $c₂) = $t * ($c₂ / $c₁)) q(@Rewrite.div_by_const_elim_real_pos $t $c₁ $c₂)
      else
        addThm q($t / (-$c₁ / $c₂) = $t * (-$c₂ / $c₁)) q(@Rewrite.div_by_const_elim_real_neg $t $c₁ $c₂)
  | .ARITH_PLUS_ZERO =>
    if pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc Real _) q(@add_zero Real _) q(@Rewrite.plus_zero) args)
  | .ARITH_MUL_ONE =>
    if pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc Real _) q(@mul_one Real _) q(@Rewrite.mul_one) args)
  | .ARITH_MUL_ZERO =>
    if pf.getArguments[1]![0]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc Real _) q(@mul_one Real _) q(@Rewrite.mul_zero) args)
  | .ARITH_DIV_TOTAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let h : Q($s ≠ 0) ← reconstructProof pf.getChildren[0]!
    addThm q($t / $s = $t / $s) q(@Rewrite.div_total $t $s $h)
  | .ARITH_NEG_NEG_ONE =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(-1 * (-1 * $t) = $t) q(@Rewrite.neg_neg_one $t)
  | .ARITH_ELIM_UMINUS =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(-$t = -1 * $t) q(@Rewrite.elim_uminus $t)
  | .ARITH_ELIM_MINUS =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q($t - $s = $t + -1 * $s) q(@Rewrite.elim_minus $t $s)
  | .ARITH_ELIM_GT =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t > $s) = ¬($t ≤ $s)) q(@Rewrite.elim_gt $t $s)
  | .ARITH_ELIM_LT =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t < $s) = ¬($t ≥ $s)) q(@Rewrite.elim_lt $t $s)
  | .ARITH_ELIM_LEQ =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≤ $s) = ($s ≥ $t)) q(@Rewrite.elim_leq $t $s)
  | .ARITH_GEQ_NORM1 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = ($t - $s ≥ 0)) q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_GEQ_NORM2 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = (-$t ≤ -$s)) q(@Rewrite.geq_norm2 $t $s)
  | .ARITH_REFL_LEQ =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≤ $t) = True) q(@Rewrite.refl_leq $t)
  | .ARITH_REFL_LT =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t < $t) = False) q(@Rewrite.refl_lt $t)
  | .ARITH_REFL_GEQ =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t ≥ $t) = True) q(@Rewrite.refl_geq $t)
  | .ARITH_REFL_GT =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t > $t) = False) q(@Rewrite.refl_gt $t)
  | .ARITH_PLUS_FLATTEN =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc Real _) q(@add_zero Real _) q(@Rewrite.plus_flatten) args)
  | .ARITH_MULT_FLATTEN =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc Real _) q(@mul_one Real _) q(@Rewrite.mult_flatten) args)
  | .ARITH_MULT_DIST =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc Real _) q(@mul_one Real _) q(@Rewrite.mult_dist) args)
  | .ARITH_PLUS_CANCEL1 =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@mul_assoc Real _) q(@mul_one Real _) q(@Rewrite.plus_cancel1) args)
  | .ARITH_PLUS_CANCEL2 =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@add_assoc Real _) q(@add_zero Real _) q(@Rewrite.plus_cancel2) args)
  | .ARITH_ABS_ELIM =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
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
    let l : Q(Real) ← reconstructTerm p.getResult[0]!
    let r : Q(Real) ← reconstructTerm p.getResult[1]!
    let lsl := q($ls + $l)
    let rsr := q($rs + $r)
    let k := p.getResult.getKind
    if ks == .LT && k == .LT then
      let hs : Q($ls < $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₁ $hs $h))
    else if ks == .LT && k == .LEQ then
      let hs : Q($ls < $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₂ $hs $h))
    else if ks == .LT && k == .EQUAL then
      let hs : Q($ls < $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₃ $hs $h))
    else if ks == .LEQ && k == .LT then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₄ $hs $h))
    else if ks == .LEQ && k == .LEQ then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₅ $hs $h))
    else if ks == .LEQ && k == .EQUAL then
      let hs : Q($ls ≤ $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₆ $hs $h))
    else if ks == .EQUAL && k == .LT then
      let hs : Q($ls = $rs) := hs
      let h : Q($l < $r) ← reconstructProof p
      return (.LT, lsl, rsr, q(Real.sum_ub₇ $hs $h))
    else if ks == .EQUAL && k == .LEQ then
      let hs : Q($ls = $rs) := hs
      let h : Q($l ≤ $r) ← reconstructProof p
      return (.LEQ, lsl, rsr, q(Real.sum_ub₈ $hs $h))
    else if ks == .EQUAL && k == .EQUAL then
      let hs : Q($ls = $rs) := hs
      let h : Q($l = $r) ← reconstructProof p
      return (.EQUAL, lsl, rsr, q(Real.sum_ub₉ $hs $h))
    else
      throwError "[sum_ub]: invalid kinds: {ks}, {p.getResult.getKind}"
  let k := pf.getChildren[0]!.getResult.getKind
  let ls : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
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
        let a : Q(Real) ← reconstructTerm vs[0]!
        let ha : Q($a ≠ 0) := hs[map.find! vs[0]!]!
        go vs ts hs map .GT q($a * $a) q(Real.mul_sign₀ $ha) 2
      else
        let a : Q(Real) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map.find! vs[0]!]!.getKind a hs[map.find! vs[0]!]! 1
    Meta.mkLambdaFVars hs h
  addThm q(andN $ps → $q) q(Builtin.scopes $h)
where
  go vs ts hs map ka (a : Q(Real)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Real) ← reconstructTerm vs[i]
      let k := ts[map.find! vs[i]]!.getKind
      if ka == .LT && k == .LT then
        let ha : Q($a < 0) := ha
        let hb : Q($b < 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b) q(Real.mul_sign₁ $ha $hb) (i + 1)
      else if ka == .LT && k == .NOT then
        let ha : Q($a < 0) := ha
        let hb : Q($b ≠ 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b * $b) q(Real.mul_sign₂ $ha $hb) (i + 2)
      else if ka == .LT && k == .GT then
        let ha : Q($a < 0) := ha
        let hb : Q($b > 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b) q(Real.mul_sign₃ $ha $hb) (i + 1)
      else if ka == .GT && k == .LT then
        let ha : Q($a > 0) := ha
        let hb : Q($b < 0) := hs[map.find! vs[i]]!
        go vs ts hs map .LT q($a * $b) q(Real.mul_sign₄ $ha $hb) (i + 1)
      else if ka == .GT && k == .NOT then
        let ha : Q($a > 0) := ha
        let hb : Q($b ≠ 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b * $b) q(Real.mul_sign₅ $ha $hb) (i + 2)
      else if ka == .GT && k == .GT then
        let ha : Q($a > 0) := ha
        let hb : Q($b > 0) := hs[map.find! vs[i]]!
        go vs ts hs map .GT q($a * $b) q(Real.mul_sign₆ $ha $hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

@[smt_proof_reconstruct] def reconstructRealProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .EVALUATE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    let h : Q(Decidable ($t = $t')) ← Meta.synthInstance q(Decidable ($t = $t'))
    if !(h.getUsedConstants.any (isNoncomputable (← getEnv))) then
      return none
    addTac q($t = $t') Real.normNum
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if pf.getResult[0]!.getSort.isInteger then return none
    reconstructSumUB pf
  | .INT_TIGHT_UB =>
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i < $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≤ ⌊$c⌋) q(@Real.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i > $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≥ ⌈$c⌉) q(@Real.int_tight_lb $c $i $h)
  | .ARITH_TRICHOTOMY =>
    if pf.getResult[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm pf.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getResult[1]!
    let k₁ := pf.getChildren[0]!.getResult.getKind
    let k₂ := pf.getChildren[1]!.getResult.getKind
    if k₁ == .LEQ && k₂ == .NOT then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Real.trichotomy₁ $h₁ $h₂)
    else if k₁ == .LEQ && k₂ == .GEQ then
      let h₁ : Q($x ≤ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Real.trichotomy₂ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .LEQ then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x < $c) q(Real.trichotomy₃ $h₁ $h₂)
    else if k₁ == .NOT && k₂ == .GEQ then
      let h₁ : Q($x ≠ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≥ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Real.trichotomy₄ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .LEQ then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≤ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x = $c) q(Real.trichotomy₅ $h₁ $h₂)
    else if k₁ == .GEQ && k₂ == .NOT then
      let h₁ : Q($x ≥ $c) ← reconstructProof pf.getChildren[0]!
      let h₂ : Q($x ≠ $c) ← reconstructProof pf.getChildren[1]!
      addThm q($x > $c) q(Real.trichotomy₆ $h₁ $h₂)
    else
      return none
  | .ARITH_POLY_NORM =>
    if pf.getResult[0]!.getSort.isInteger then return none
    let a : Q(Real) ← reconstructTerm pf.getResult[0]!
    let b : Q(Real) ← reconstructTerm pf.getResult[1]!
    addTac q($a = $b) Real.polyNorm
  | .ARITH_POLY_NORM_REL =>
    if pf.getResult[0]![0]!.getSort.isInteger then return none
    let cx : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let x₁ : Q(Real) ← reconstructTerm pf.getResult[0]![0]!
    let x₂ : Q(Real) ← reconstructTerm pf.getResult[0]![1]!
    let cy : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]![0]!
    let y₁ : Q(Real) ← reconstructTerm pf.getResult[1]![0]!
    let y₂ : Q(Real) ← reconstructTerm pf.getResult[1]![1]!
    let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructProof pf.getChildren[0]!
    let k := pf.getResult[0]!.getKind
    if k == .EQUAL then
      let hcx : Q($cx ≠ 0) ← Meta.mkFreshExprMVar q($cx ≠ 0)
      let hcy : Q($cy ≠ 0) ← Meta.mkFreshExprMVar q($cy ≠ 0)
      Real.normNum hcx.mvarId!
      Real.normNum hcy.mvarId!
      addThm q(($x₁ = $x₂) = ($y₁ = $y₂)) q(Real.eq_of_sub_eq $hcx $hcy $h)
    else if pf.getChildren[0]!.getResult[0]![0]!.getRationalValue > 0 then
      let hcx : Q($cx > 0) ← Meta.mkFreshExprMVar q($cx > 0)
      let hcy : Q($cy > 0) ← Meta.mkFreshExprMVar q($cy > 0)
      Real.normNum hcx.mvarId!
      Real.normNum hcy.mvarId!
      match k with
      | .LT =>
        addThm q(($x₁ < $x₂) = ($y₁ < $y₂)) q(lt_of_sub_eq_pos $hcx $hcy $h)
      | .LEQ =>
        addThm q(($x₁ ≤ $x₂) = ($y₁ ≤ $y₂)) q(Real.le_of_sub_eq_pos $hcx $hcy $h)
      | .GEQ =>
        addThm q(($x₁ ≥ $x₂) = ($y₁ ≥ $y₂)) q(Real.ge_of_sub_eq_pos $hcx $hcy $h)
      | .GT =>
        addThm q(($x₁ > $x₂) = ($y₁ > $y₂)) q(Real.gt_of_sub_eq_pos $hcx $hcy $h)
      | _   => return none
    else
      let hcx : Q($cx < 0) ← Meta.mkFreshExprMVar q($cx < 0)
      let hcy : Q($cy < 0) ← Meta.mkFreshExprMVar q($cy < 0)
      Real.normNum hcx.mvarId!
      Real.normNum hcy.mvarId!
      match k with
      | .LT =>
        addThm q(($x₁ < $x₂) = ($y₁ < $y₂)) q(Real.lt_of_sub_eq_neg $hcx $hcy $h)
      | .LEQ =>
        addThm q(($x₁ ≤ $x₂) = ($y₁ ≤ $y₂)) q(Real.le_of_sub_eq_neg $hcx $hcy $h)
      | .GEQ =>
        addThm q(($x₁ ≥ $x₂) = ($y₁ ≥ $y₂)) q(Real.ge_of_sub_eq_neg $hcx $hcy $h)
      | .GT =>
        addThm q(($x₁ > $x₂) = ($y₁ > $y₂)) q(Real.gt_of_sub_eq_neg $hcx $hcy $h)
      | _   => return none
  | .ARITH_MULT_SIGN =>
    if pf.getResult[1]![0]!.getSort.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if pf.getArguments[0]!.getSort.isInteger then return none
    let m : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m > 0 ∧ $l < $r → $m * $l < $m * $r) q(@Real.mul_pos_lt $l $r $m)
    | .LEQ =>
      addThm q($m > 0 ∧ $l ≤ $r → $m * $l ≤ $m * $r) q(@Real.mul_pos_le $l $r $m)
    | .EQUAL =>
      addThm q($m > 0 ∧ $l = $r → $m * $l = $m * $r) q(@Real.mul_pos_eq $l $r $m)
    | .GEQ =>
      addThm q($m > 0 ∧ $l ≥ $r → $m * $l ≥ $m * $r) q(@Real.mul_pos_ge $l $r $m)
    | .GT =>
      addThm q($m > 0 ∧ $l > $r → $m * $l > $m * $r) q(@Real.mul_pos_gt $l $r $m)
    | _ => return none
  | .ARITH_MULT_NEG =>
    if pf.getArguments[0]!.getSort.isInteger then return none
    let m : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[1]![0]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[1]![1]!
    match pf.getArguments[1]!.getKind with
    | .LT =>
      addThm q($m < 0 ∧ $l < $r → $m * $l > $m * $r) q(@Real.mul_neg_lt $l $r $m)
    | .LEQ =>
      addThm q($m < 0 ∧ $l ≤ $r → $m * $l ≥ $m * $r) q(@Real.mul_neg_le $l $r $m)
    | .EQUAL =>
      addThm q($m < 0 ∧ $l = $r → $m * $l = $m * $r) q(@Real.mul_neg_eq $l $r $m)
    | .GEQ =>
      addThm q($m < 0 ∧ $l ≥ $r → $m * $l ≤ $m * $r) q(@Real.mul_neg_ge $l $r $m)
    | .GT =>
      addThm q($m < 0 ∧ $l > $r → $m * $l < $m * $r) q(@Real.mul_neg_gt $l $r $m)
    | _ => return none
  | .ARITH_MULT_TANGENT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let a : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let b : Q(Real) ← reconstructTerm pf.getArguments[3]!
    if pf.getArguments[4]!.getIntegerValue == -1 then
      addThm q(($x * $y ≤ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≥ $b ∨ $x ≥ $a ∧ $y ≤ $b)) q(@Real.mul_tangent_lower_eq $a $b $x $y)
    else
      addThm q(($x * $y ≥ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≤ $b ∨ $x ≥ $a ∧ $y ≥ $b)) q(@Real.mul_tangent_upper_eq $a $b $x $y)
  | _ => return none

end Smt.Reconstruct.Real
