/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruct
import Smt.Reconstruct.Builtin.Lemmas
import Smt.Reconstruct.Real.Lemmas
import Smt.Reconstruct.Real.Polynorm
import Smt.Reconstruct.Real.Rewrites
import Smt.Reconstruct.Real.TransFns
import Smt.Reconstruct.Rewrite

namespace Smt.Reconstruct.Real

open Lean Qq

@[smt_sort_reconstruct] def reconstructRealSort : SortReconstructor := fun s => do match s.getKind with
  | .REAL_SORT => return q(Real)
  | _          => return none

@[smt_term_reconstruct] def reconstructReal : TermReconstructor := fun t => do match t.getKind with
  | .SKOLEM => match t.getSkolemId! with
    | .DIV_BY_ZERO => return q(fun (x : Real) => x / 0)
    | .TRANSCENDENTAL_PURIFY_ARG =>
      let .app _ x ← reconstructTerm t.getSkolemIndices![0]! | return none
      let x : Q(Real) := x
      let s : Q(Real) := q(Classical.epsilon (TransFns.shift_prop_part $x))
      let y : Q(Real) := q(Classical.epsilon (TransFns.shift_prop $x $s))
      return y
    | .TRANSCENDENTAL_SINE_PHASE_SHIFT =>
      let X : Q(Real) ← reconstructTerm t.getSkolemIndices![0]!
      let s : Q(Real) := q(Classical.epsilon (TransFns.shift_prop_part $X))
      return s
    | _ => return none
  | .CONST_RATIONAL =>
    let c : Std.Internal.Rat := t.getRationalValue!
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
    return q(|$x|)
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
  | .EXPONENTIAL =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.exp $x)
  | .SINE =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.sin $x)
  | .COSINE =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.cos $x)
  | .TANGENT =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.tan $x)
  | .COTANGENT =>
    if t.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm t[0]!
    return q(Real.cot $x)
  | .PI => return q(Real.pi)
  | _ => return none
where
  mkRealLit (n : Nat) : Q(Real) := match h : n with
    | 0     => q(0 : Real)
    | 1     => q(1 : Real)
    | _ + 2 =>
      let h : Q(Nat.AtLeastTwo $n) := h ▸ q(Nat.instAtLeastTwo)
      let h := mkApp3 q(@instOfNatAtLeastTwo Real) (mkRawNatLit n) q(Real.instNatCast) h
      mkApp2 q(@OfNat.ofNat Real) (mkRawNatLit n) h
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .ARITH_POW_ELIM =>
    if (pf.getResult[0]!)[0]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm (pf.getResult[0]!)[0]!
    let c : Nat := (pf.getResult[0]!)[1]!.getIntegerValue!.toNat
    let y : Q(Real) ← reconstructTerm pf.getResult[1]!
    let mut h : Q($x ^ $c = $y) := .app q(@Eq.refl Real) y
    if c > 0 then
      let qPow : Q(Real) := c.repeat (fun acc => q($acc * $x)) (.bvar 0)
      let p : Q(Real → Prop) := .lam `x q(Real) q($qPow = $y) .default
      h := .app q(Eq.subst (motive := $p) (one_mul $x).symm) h
    addThm q($x ^ $c = $y) h
  | .ARITH_DIV_TOTAL_ZERO_REAL =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q($x / 0 = 0) q(@Rewrite.div_total_zero $x)
  | .ARITH_ELIM_GT =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t > $s) = ¬($s ≥ $t)) q(@Rewrite.elim_gt $t $s)
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
  | .ARITH_GEQ_NORM1_REAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≥ $s) = ($t - $s ≥ 0)) q(@Rewrite.geq_norm1 $t $s)
  | .ARITH_EQ_ELIM_REAL =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t = $s) = ($t ≥ $s ∧ $t ≤ $s)) q(@Rewrite.eq_elim $t $s)
  | .ARITH_INT_EQ_CONFLICT =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let h : Q((↑⌊$c⌋ = $c) = False) ← reconstructProof pf.getChildren[0]!
    addThm q(($t = $c) = False) q(@Rewrite.eq_conflict $t $c $h)
  | .ARITH_INT_GEQ_TIGHTEN =>
    let t : Q(Int) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let cc : Q(Int) ← reconstructTerm pf.getArguments[3]!
    let hc : Q((↑⌊$c⌋ = $c) = False) ← reconstructProof pf.getChildren[0]!
    let hcc : Q($cc = Int.addN [⌊$c⌋, 1]) ← reconstructProof pf.getChildren[1]!
    addThm q(($t ≥ $c) = ($t ≥ $cc)) q(@Rewrite.geq_tighten $t $c $cc $hc $hcc)
  | .ARITH_ABS_EQ =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((|$x| = |$y|) = ($x = $y ∨ $x = -$y)) q(@Rewrite.abs_eq $x $y)
  | .ARITH_ABS_REAL_GT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let y : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((|$x| > |$y|) = ite ($x ≥ 0) (ite ($y ≥ 0) ($x > $y) ($x > -$y)) (ite ($y ≥ 0) (-$x > $y) (-$x > -$y)))
           q(@Rewrite.abs_gt $x $y)
  | .ARITH_GEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s ≥ $r) = ite $c ($t ≥ $r) ($s ≥ $r)) q(@Rewrite.geq_ite_lift $c $hc $t $s $r)
  | .ARITH_LEQ_ITE_LIFT =>
    if pf.getArguments[2]!.getSort.isInteger then return none
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let t : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let r : Q(Real) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s ≤ $r) = ite $c ($t ≤ $r) ($s ≤ $r)) q(@Rewrite.leq_ite_lift $c $hc $t $s $r)
  | .ARITH_MIN_LT1 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t < $s) $t $s ≤ $t) = True) q(@Rewrite.min_lt1 $t $s)
  | .ARITH_MIN_LT2 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t < $s) $t $s ≤ $s) = True) q(@Rewrite.min_lt2 $t $s)
  | .ARITH_MAX_GEQ1 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t ≥ $s) $t $s ≥ $t) = True) q(@Rewrite.max_geq1 $t $s)
  | .ARITH_MAX_GEQ2 =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let s : Q(Real) ← reconstructTerm pf.getArguments[2]!
    addThm q((ite ($t ≥ $s) $t $s ≥ $s) = True) q(@Rewrite.max_geq2 $t $s)
  | .ARITH_SINE_ZERO =>
    addThm q(Real.sin 0 = 0) q(Rewrite.arith_sine_zero)
  | .ARITH_SINE_PI2 =>
    addThm q(Real.sin ((1 / 2) * Real.pi) = 1) q(Rewrite.arith_sine_pi2)
  | .ARITH_COSINE_ELIM =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(Real.cos $t = Real.sin ((1 / 2) * Real.pi - $t)) q(Rewrite.arith_cosine_elim $t)
  | .ARITH_TANGENT_ELIM =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(Real.tan $t = Real.sin $t / Real.cos $t) q(Rewrite.arith_tangent_elim $t)
  | .ARITH_COTANGENT_ELIM =>
    if pf.getArguments[1]!.getSort.isInteger then return none
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addThm q(Real.cot $t = Real.cos $t / Real.sin $t) q(Rewrite.arith_cotangent_elim $t)
  | _ => return none

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
      throwError "[sum_ub]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind
  let ls : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
  let rs : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addThm (if ks == .LT then q($ls < $rs) else q($ls ≤ $rs)) hs

def reconstructMulAbsComparison (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let f := fun (ks, ls, rs, hs) p => do
    let k := p.getResult.getKind
    if ks == .EQUAL && k == .EQUAL then
      let l : Q(Real) ← reconstructTerm (p.getResult[0]!)[0]!
      let r : Q(Real) ← reconstructTerm (p.getResult[1]!)[0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(|$ls| = |$rs|) := hs
      let h : Q(|$l| = |$r|) ← reconstructProof p
      return (.EQUAL, lsl, rsr, q(Real.mul_abs₁ $hs $h))
    else if ks == .GT && k == .AND then
      let r : Q(Real) ← reconstructTerm ((p.getResult[0]!)[1]!)[0]!
      let l : Q(Real) ← reconstructTerm ((p.getResult[0]!)[0]!)[0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(|$ls| > |$rs|) := hs
      let h : Q(|$l| = |$r| ∧ $l ≠ 0) ← reconstructProof p
      return (.GT, lsl, rsr, q(Real.mul_abs₂ $hs $h))
    else if ks == .GT && k == .GT then
      let l : Q(Real) ← reconstructTerm (p.getResult[0]!)[0]!
      let r : Q(Real) ← reconstructTerm (p.getResult[1]!)[0]!
      let lsl := q($ls * $l)
      let rsr := q($rs * $r)
      let hs : Q(|$ls| > |$rs|) := hs
      let h : Q(|$l| > |$r|) ← reconstructProof p
      return (.GT, lsl, rsr, q(Real.mul_abs₃ $hs $h))
    else
      throwError "[mul_abs]: invalid kinds: {ks}, {k}"
  let k := pf.getChildren[0]!.getResult.getKind
  let ls : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[0]!)[0]!
  let rs : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[1]!)[0]!
  let hs ← reconstructProof pf.getChildren[0]!
  let (ks, ls, rs, hs) ← pf.getChildren[1:].foldlM f (k, ls, rs, hs)
  addThm (if ks == .EQUAL then q($ls = $rs) else q($ls > $rs)) hs

def reconstructMulSign (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let ts := if pf.getResult[0]!.getKind == .AND then pf.getResult[0]!.getChildren else #[pf.getResult[0]!]
  let mut hs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
  let mut map : Std.HashMap cvc5.Term Nat := {}
  for h : i in [0:ts.size] do
    let t := ts[i]
    let p : Q(Prop) ← reconstructTerm t
    hs := hs.push (Name.num `a i, fun _ => return p)
    map := map.insert (if t.getKind == .NOT then (t[0]!)[0]! else t[0]!) i
  let t := pf.getResult[1]!
  let vs := if t[0]!.getKind == .CONST_INTEGER then t[1]!.getChildren else t[0]!.getChildren
  let f t ps := do
    let p : Q(Prop) ← reconstructTerm t
    return q($p :: $ps)
  let ps : Q(List Prop) ← ts.foldrM f q([])
  let q : Q(Prop) ← reconstructTerm t
  let h : Q(impliesN $ps $q) ← Meta.withLocalDeclsD hs fun hs => do
    let h : Q($q) ← if ts[map[vs[0]!]!]!.getKind == .NOT then
        let a : Q(Real) ← reconstructTerm vs[0]!
        let ha : Q($a ≠ 0) := hs[map[vs[0]!]!]!
        go vs ts hs map .GT q($a * $a) q(Real.mul_sign₀ $ha) 2
      else
        let a : Q(Real) ← reconstructTerm vs[0]!
        go vs ts hs map ts[map[vs[0]!]!]!.getKind a hs[map[vs[0]!]!]! 1
    Meta.mkLambdaFVars hs h
  addThm q(andN $ps → $q) q(Builtin.scopes $h)
where
  go vs ts hs map (ka : cvc5.Kind) (a : Q(Real)) (ha : Expr) i : ReconstructM Expr := do
    if hi : i < vs.size then
      let b : Q(Real) ← reconstructTerm vs[i]
      let k : cvc5.Kind := ts[map[vs[i]]!]!.getKind
      if ka == .LT && k == .LT then
        let ha : Q($a < 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Real.mul_sign₁ $ha $hb) (i + 1)
      else if ka == .LT && k == .NOT then
        let ha : Q($a < 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b * $b) q(Real.mul_sign₂ $ha $hb) (i + 2)
      else if ka == .LT && k == .GT then
        let ha : Q($a < 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Real.mul_sign₃ $ha $hb) (i + 1)
      else if ka == .GT && k == .LT then
        let ha : Q($a > 0) := ha
        let hb : Q($b < 0) := hs[map[vs[i]]!]!
        go vs ts hs map .LT q($a * $b) q(Real.mul_sign₄ $ha $hb) (i + 1)
      else if ka == .GT && k == .NOT then
        let ha : Q($a > 0) := ha
        let hb : Q($b ≠ 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b * $b) q(Real.mul_sign₅ $ha $hb) (i + 2)
      else if ka == .GT && k == .GT then
        let ha : Q($a > 0) := ha
        let hb : Q($b > 0) := hs[map[vs[i]]!]!
        go vs ts hs map .GT q($a * $b) q(Real.mul_sign₆ $ha $hb) (i + 1)
      else
        throwError "[mul_sign]: invalid kinds: {ka}, {k}"
    else
      return ha

def reconstructArithPolyNormRel (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let lcx : Std.Internal.Rat := (pf.getChildren[0]!.getResult[0]!)[0]!.getRationalValue!
  let cx : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[0]!)[0]!
  let cy : Q(Real) ← reconstructTerm (pf.getChildren[0]!.getResult[1]!)[0]!
  let x₁ : Q(Real) ← reconstructTerm (pf.getResult[0]!)[0]!
  let x₂ : Q(Real) ← reconstructTerm (pf.getResult[0]!)[1]!
  let y₁ : Q(Real) ← reconstructTerm (pf.getResult[1]!)[0]!
  let y₂ : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
  let h : Q($cx * ($x₁ - $x₂) = $cy * ($y₁ - $y₂)) ← reconstructProof pf.getChildren[0]!
  let k := pf.getResult[0]!.getKind
  let (hcx, hcy) :=
    if k == .EQUAL then (q($cx ≠ 0), q($cy ≠ 0))
    else if lcx > 0 then (q($cx > 0), q($cy > 0))
    else (q($cx < 0), q($cy < 0))
  let hcx ← Meta.mkFreshExprMVar hcx
  let hcy ← Meta.mkFreshExprMVar hcy
  Real.normNum hcx.mvarId!
  Real.normNum hcy.mvarId!
  let n ← getThmName k (pf.getResult[0]!)[0]!.getSort.isInteger (pf.getResult[1]!)[0]!.getSort.isInteger (lcx > 0)
  return mkApp9 (.const n []) x₁ x₂ y₁ y₂ cx cy hcx hcy h
where
  getThmName (k : cvc5.Kind) (il ir sign : Bool) : ReconstructM Name :=
    if k == .LT && il == false && ir == false && sign == true then pure ``Real.lt_of_sub_eq_pos
    else if k == .LT && il == false && ir == false && sign == false then pure ``Real.lt_of_sub_eq_neg
    else if k == .LT && il == false && ir == true && sign == true then pure ``Real.lt_of_sub_eq_pos_int_right
    else if k == .LT && il == false && ir == true && sign == false then pure ``Real.lt_of_sub_eq_neg_int_right
    else if k == .LT && il == true && ir == false && sign == true then pure ``Real.lt_of_sub_eq_pos_int_left
    else if k == .LT && il == true && ir == false && sign == false then pure ``Real.lt_of_sub_eq_neg_int_left
    else if k == .LEQ && il == false && ir == false && sign == true then pure ``Real.le_of_sub_eq_pos
    else if k == .LEQ && il == false && ir == false && sign == false then pure ``Real.le_of_sub_eq_neg
    else if k == .LEQ && il == false && ir == true && sign == true then pure ``Real.le_of_sub_eq_pos_int_right
    else if k == .LEQ && il == false && ir == true && sign == false then pure ``Real.le_of_sub_eq_neg_int_right
    else if k == .LEQ && il == true && ir == false && sign == true then pure ``Real.le_of_sub_eq_pos_int_left
    else if k == .LEQ && il == true && ir == false && sign == false then pure ``Real.le_of_sub_eq_neg_int_left
    else if k == .EQUAL && il == false && ir == false then pure ``Real.eq_of_sub_eq
    else if k == .EQUAL && il == false && ir == true then pure ``Real.eq_of_sub_eq_int_right
    else if k == .EQUAL && il == true && ir == false then pure ``Real.eq_of_sub_eq_int_left
    else if k == .GEQ && il == false && ir == false && sign == true then pure ``Real.ge_of_sub_eq_pos
    else if k == .GEQ && il == false && ir == false && sign == false then pure ``Real.ge_of_sub_eq_neg
    else if k == .GEQ && il == false && ir == true && sign == true then pure ``Real.ge_of_sub_eq_pos_int_right
    else if k == .GEQ && il == false && ir == true && sign == false then pure ``Real.ge_of_sub_eq_neg_int_right
    else if k == .GEQ && il == true && ir == false && sign == true then pure ``Real.ge_of_sub_eq_pos_int_left
    else if k == .GEQ && il == true && ir == false && sign == false then pure ``Real.ge_of_sub_eq_neg_int_left
    else if k == .GT && il == false && ir == false && sign == true then pure ``Real.gt_of_sub_eq_pos
    else if k == .GT && il == false && ir == false && sign == false then pure ``Real.gt_of_sub_eq_neg
    else if k == .GT && il == false && ir == true && sign == true then pure ``Real.gt_of_sub_eq_pos_int_right
    else if k == .GT && il == false && ir == true && sign == false then pure ``Real.gt_of_sub_eq_neg_int_right
    else if k == .GT && il == true && ir == false && sign == true then pure ``Real.gt_of_sub_eq_pos_int_left
    else if k == .GT && il == true && ir == false && sign == false then pure ``Real.gt_of_sub_eq_neg_int_left
    else throwError "[arith_poly_norm_rel]: invalid combination of kind, integer operands, and sign: {k}, {il}, {ir}, {sign}"

@[smt_proof_reconstruct] def reconstructRealProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .EVALUATE =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    let h : Q(Decidable ($t = $t')) ← Meta.synthInstance q(Decidable ($t = $t'))
    if !(h.getUsedConstants.any (isNoncomputable (← getEnv))) then
      return none
    addTac q($t = $t') normNumAbs
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .ARITH_SUM_UB =>
    if pf.getResult[0]!.getSort.isInteger then return none
    reconstructSumUB pf
  | .ARITH_MULT_ABS_COMPARISON =>
    if pf.getResult[0]!.getSort.isInteger then return none
    reconstructMulAbsComparison pf
  | .INT_TIGHT_UB =>
    if pf.getChildren[0]!.getResult[1]!.getSort.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i < $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≤ ⌈$c⌉ - 1) q(@Real.int_tight_ub $c $i $h)
  | .INT_TIGHT_LB =>
    if pf.getChildren[0]!.getResult[1]!.getSort.isInteger then return none
    let i : Q(Int) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let c : Q(Real) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let h : Q($i > $c) ← reconstructProof pf.getChildren[0]!
    addThm q($i ≥ ⌊$c⌋ + 1) q(@Real.int_tight_lb $c $i $h)
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
  | .ARITH_REDUCTION =>
    if pf.getArguments[0]!.getSort.isInteger then return none
    if pf.getArguments[0]!.getKind == .ABS then
      let x : Q(Real) ← reconstructTerm (pf.getArguments[0]!)[0]!
      addThm q(|$x| = ite ($x < 0) (-$x) $x) q(@Real.abs_elim $x)
    else
      return none
  | .ARITH_POLY_NORM =>
    if pf.getResult[0]!.getSort.isInteger then return none
    let a : Q(Real) ← reconstructTerm pf.getResult[0]!
    let b : Q(Real) ← reconstructTerm pf.getResult[1]!
    let tac := if ← useNative then Real.nativePolyNorm else Real.polyNorm
    addTac q($a = $b) tac
  | .ARITH_POLY_NORM_REL =>
    if (pf.getChildren[0]!.getResult[0]!)[0]!.getSort.isInteger then return none
    reconstructArithPolyNormRel pf
  | .ARITH_MULT_SIGN =>
    if (pf.getResult[1]!)[0]!.getSort.isInteger then return none
    reconstructMulSign pf
  | .ARITH_MULT_POS =>
    if pf.getArguments[0]!.getSort.isInteger then return none
    let m : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let l : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[0]!
    let r : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[1]!
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
    let l : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[0]!
    let r : Q(Real) ← reconstructTerm (pf.getArguments[1]!)[1]!
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
    if pf.getArguments[4]!.getBooleanValue! == false then
      addThm q(($x * $y ≤ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≥ $b ∨ $x ≥ $a ∧ $y ≤ $b)) q(@Real.mul_tangent_lower_eq $a $b $x $y)
    else
      addThm q(($x * $y ≥ $b * $x + $a * $y - $a * $b) = ($x ≤ $a ∧ $y ≤ $b ∨ $x ≥ $a ∧ $y ≥ $b)) q(@Real.mul_tangent_upper_eq $a $b $x $y)
  | .ARITH_TRANS_PI =>
    let l : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[1]!
    addTac q(Real.pi ≥ $l ∧ Real.pi ≤ $u) TransFns.arithTransPiTac
  | .ARITH_TRANS_EXP_ZERO =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q(($t = 0) = (Real.exp $t = 1)) q(TransFns.arithTransExpZeroEq $t)
  | .ARITH_TRANS_SINE_SHIFT =>
    let x : Q(Real) ← reconstructTerm pf.getArguments[0]!
    let s : Q(Real) := q(Classical.epsilon (TransFns.shift_prop_part $x))
    let y : Q(Real) := q(Classical.epsilon (TransFns.shift_prop $x $s))
    addThm q(TransFns.shift_prop $x $s $y) q(TransFns.arithTransSineShift₁ $x)
  | .ARITH_TRANS_EXP_POSITIVITY =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q(Real.exp $t > 0) q(TransFns.arithTransExpPositivity $t)
  | .ARITH_TRANS_SINE_TANGENT_PI =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q(($t > (-1) * Real.pi → Real.sin $t > (-1) * Real.pi - $t) ∧ ($t < Real.pi → Real.sin $t < Real.pi - $t)) q(TransFns.arithTransSineTangentPi $t)
  | .ARITH_TRANS_SINE_TANGENT_ZERO =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q(($t > 0 → Real.sin $t < $t) ∧ ($t < 0 → Real.sin $t > $t)) q(TransFns.arithTransSinTangentZero $t)
  | .ARITH_TRANS_EXP_SUPER_LIN =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q($t ≤ 0 ∨ Real.exp $t > $t + 1) q(TransFns.arithTransExpSuperLin $t)
  | .ARITH_TRANS_EXP_NEG =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q(($t < 0) = (Real.exp $t < 1)) q(TransFns.arithTransExpNeg' $t)
  | .ARITH_TRANS_SINE_BOUNDS =>
    let t : Q(Real) ← reconstructTerm pf.getArguments[0]!
    addThm q((Real.sin $t ≤ 1 ∧ Real.sin $t ≥ -1)) q(TransFns.arithTransSineBounds $t)
  | .ARITH_TRANS_EXP_APPROX_BELOW =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let w : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]! -- rational value of the taylor polynomial

    let poly_deg : Q(Nat) := q((2 : Nat) * (Int.natAbs $d) - 1)
    let goal : Q(Prop) := q(TransFns.expTaylor $poly_deg $c = $w)
    let (.mvar mv) ← Meta.mkFreshExprMVar (some goal) | throwError "impossible 2"
    normNumFactorial mv

    let poly_deg_is_odd : Q(Prop) := q($poly_deg = 2 * (Int.natAbs $d - 1) + 1)
    let (.mvar poly_deg_is_odd_pf) ← Meta.mkFreshExprMVar (some poly_deg_is_odd) | throwError "impossible 3"
    Real.normNum poly_deg_is_odd_pf

    let prop : Q(Prop) ← reconstructTerm pf.getResult
    let proof ← Meta.mkAppM ``TransFns.arithTransExpApproxBelowComp #[t, c, w, q(2 * (Int.natAbs $d) - 1), q((Int.natAbs $d) - 1), Expr.mvar mv, Expr.mvar poly_deg_is_odd_pf]
    addThm prop proof
  | .ARITH_TRANS_EXP_APPROX_ABOVE_POS =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let evalL : Q(Real) ← reconstructTerm ((pf.getResult[1]!)[1]!)[0]!
    let evalU : Q(Real) ← reconstructTerm (((((pf.getResult[1]!)[1]!)[1]!)[0]!)[0]!)[1]!
    let d_nat : Q(Nat) := q((Int.natAbs $d) - 1)

    let goalL : Q(Prop) := q($evalL = TransFns.expTaylor $d_nat $l / (1 - $l ^ ($d_nat + 1) / ($d_nat + 1).factorial))
    let (.mvar mvL) ← Meta.mkFreshExprMVar (some goalL) | throwError "impossible 2"
    normNumFactorial mvL

    let goalU : Q(Prop) := q($evalU = TransFns.expTaylor $d_nat $u / (1 - $u ^ ($d_nat + 1) / ($d_nat + 1).factorial))
    let (.mvar mvU) ← Meta.mkFreshExprMVar (some goalU) | throwError "impossible 2"
    normNumFactorial mvU

    let goal_l_nonneg : Q(Prop) := q(0 ≤ $l)
    let (.mvar mv_l_nonneg) ← Meta.mkFreshExprMVar (some goal_l_nonneg) | throwError "impossible 3"
    normNumFactorial mv_l_nonneg

    let goal_bound_u : Q(Prop) := q($u ^ ($d_nat + 1) < Nat.factorial ($d_nat + 1))
    let (.mvar mv_bound_u) ← Meta.mkFreshExprMVar (some goal_bound_u) | throwError "impossible 4"
    normNumFactorial mv_bound_u

    let prop ← reconstructTerm pf.getResult
    let proof ← Meta.mkAppM ``TransFns.arithTransExpApproxAbovePosComp #[d_nat, l, u, t, evalL, evalU, .mvar mv_l_nonneg, .mvar mv_bound_u, .mvar mvL, .mvar mvU]
    addThm prop proof
  | .ARITH_TRANS_EXP_APPROX_ABOVE_NEG =>
    let evalL : Q(Real) ← reconstructTerm ((pf.getResult[1]!)[1]!)[0]!
    let evalU : Q(Real) ← reconstructTerm (((((pf.getResult[1]!)[1]!)[1]!)[0]!)[0]!)[1]!
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let d_nat : Q(Nat) := q(Int.natAbs $d)
    let d_half : Q(Nat) := q(Nat.div $d_nat 2)

    let goalL : Q(Prop) := q(TransFns.expTaylor $d_nat $l = $evalL)
    let (.mvar mvL) ← Meta.mkFreshExprMVar (some goalL) | throwError "impossible 2"
    normNumFactorial mvL

    let goalU : Q(Prop) := q(TransFns.expTaylor $d_nat $u = $evalU)
    let (.mvar mvU) ← Meta.mkFreshExprMVar (some goalU) | throwError "impossible 2"
    normNumFactorial mvU

    let goalDeg : Q(Prop) := q($d_nat = 2 * $d_half)
    let (.mvar goalDeg_pf) ← Meta.mkFreshExprMVar (some goalDeg) | throwError "impossible 3"
    normNumFactorial goalDeg_pf

    let uNeg : Q(Prop) := q($u < 0)
    let (.mvar uNeg_pf) ← Meta.mkFreshExprMVar (some uNeg) | throwError "impossible 4"
    Real.normNum uNeg_pf

    let prop : Q(Prop) ← reconstructTerm pf.getResult
    let proof ← Meta.mkAppM ``TransFns.arithTransExpApproxAboveNegComp #[d_nat, d_half, l, u, t, evalL, evalU, .mvar mvL, .mvar mvU, .mvar goalDeg_pf, .mvar uNeg_pf]
    addThm prop proof
  | .ARITH_TRANS_SINE_APPROX_BELOW_NEG =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let eval_c : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
    let real_d : Q(Nat) := q(Int.natAbs $d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)

    let goalDeg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let (.mvar goalDeg_pf) ← Meta.mkFreshExprMVar (some goalDeg) | throwError "impossible 3"
    normNumFactorial goalDeg_pf

    let goal_l_bound : Q(Prop) := q(-Real.pi ≤ $lb)
    let (.mvar mv_l_bound) ← Meta.mkFreshExprMVar (some goal_l_bound) | throwError "impossible 3"
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := mv_l_bound)

    let ubBound : Q(Prop) := q($ub ≤ 0)
    let (.mvar ubBound_pf) ← Meta.mkFreshExprMVar (some ubBound) | throwError "impossible 4"
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ubBound_pf)

    let goalC : Q(Prop) := q($eval_c = TransFns.sinTaylor $real_d $c - ($c ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvC) ← Meta.mkFreshExprMVar (some goalC) | throwError "impossible 2"
    normNumFactorial mvC

    let goalIf : Q(Prop) := q($c = if -Real.pi/2 < $lb then $lb else if - Real.pi/2 < $ub then -Real.pi/2 else $ub)
    let (.mvar if_proof) ← Meta.mkFreshExprMVar (some goalIf) | throwError "impossible 4"
    let some [if1, if2] ← Meta.splitTarget? if_proof | throwError "split 1"

    let some [if3, if4] ← Meta.splitTarget? if2 | throwError "split 2"

    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if1)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if3)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if4)

    let prop : Q(Prop) ← reconstructTerm pf.getResult
    let proof ← Meta.mkAppM ``TransFns.arithTransSineApproxBelowNegComp
      #[real_d, d_half, lb, ub, t, c, eval_c, .mvar goalDeg_pf, .mvar mvC,  .mvar mv_l_bound, .mvar ubBound_pf, .mvar if_proof]
    addThm prop proof
  | .ARITH_TRANS_SINE_APPROX_ABOVE_NEG =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[5]!
    let real_d : Q(Nat) := q(Int.natAbs $d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)

    let goalDeg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let (.mvar goalDeg_pf) ← Meta.mkFreshExprMVar (some goalDeg) | throwError "impossible 3"
    normNumFactorial goalDeg_pf

    let ubNonpos : Q(Prop) := q($ub ≤ 0)
    let (.mvar ubNonpos_pf) ← Meta.mkFreshExprMVar (some ubNonpos) | throwError "impossible 4"
    Real.normNum ubNonpos_pf

    let lbBound : Q(Prop) := q(-Real.pi ≤ $lb)
    let (.mvar lbBound_pf) ← Meta.mkFreshExprMVar (some lbBound) | throwError "impossible 4"
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := lbBound_pf)

    let goalL : Q(Prop) := q($l = TransFns.sinTaylor $real_d $lb + ($lb ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvL) ← Meta.mkFreshExprMVar (some goalL) | throwError "impossible 2"
    normNumFactorial mvL

    let goalU : Q(Prop) := q($u = TransFns.sinTaylor $real_d $ub + ($ub ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvU) ← Meta.mkFreshExprMVar (some goalU) | throwError "impossible 2"
    normNumFactorial mvU

    let prop ← reconstructTerm pf.getResult
    let pf ← Meta.mkAppM ``TransFns.arithTransSineApproxAboveNegComp
      #[real_d, d_half, lb, ub, t, l, u, .mvar goalDeg_pf, .mvar ubNonpos_pf, .mvar lbBound_pf, .mvar mvL, .mvar mvU]
    addThm prop pf
  | .ARITH_TRANS_SINE_APPROX_BELOW_POS =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let l : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let u : Q(Real) ← reconstructTerm pf.getArguments[5]!
    let real_d : Q(Nat) := q(Int.natAbs $d - 1)

    let lbNonneg : Q(Prop) := q(0 ≤ $lb)
    let (.mvar lbNonneg_pf) ← Meta.mkFreshExprMVar (some lbNonneg) | throwError "impossible 4"
    Real.normNum lbNonneg_pf

    let ubBound : Q(Prop) := q($ub ≤ Real.pi)
    let (.mvar ubBound_pf) ← Meta.mkFreshExprMVar (some ubBound) | throwError "impossible 4"
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ubBound_pf)

    let goalL : Q(Prop) := q($l = TransFns.sinTaylor $real_d $lb - ($lb ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvL) ← Meta.mkFreshExprMVar (some goalL) | throwError "impossible 2"
    normNumFactorial mvL

    let goalU : Q(Prop) := q($u = TransFns.sinTaylor $real_d $ub - ($ub ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvU) ← Meta.mkFreshExprMVar (some goalU) | throwError "impossible 2"
    normNumFactorial mvU

    let prop ← reconstructTerm pf.getResult
    let pf ← Meta.mkAppM ``TransFns.arithTransSineApproxBelowPosComp
      #[real_d, t, lb, ub, l, u, .mvar lbNonneg_pf, .mvar ubBound_pf, .mvar mvL, .mvar mvU]
    addThm prop pf
  | .ARITH_TRANS_SINE_APPROX_ABOVE_POS =>
    let d : Q(Int) ← reconstructTerm pf.getArguments[0]!
    let t : Q(Real) ← reconstructTerm pf.getArguments[1]!
    let c : Q(Real) ← reconstructTerm pf.getArguments[2]!
    let lb : Q(Real) ← reconstructTerm pf.getArguments[3]!
    let ub : Q(Real) ← reconstructTerm pf.getArguments[4]!
    let eval_c : Q(Real) ← reconstructTerm (pf.getResult[1]!)[1]!
    let real_d : Q(Nat) := q(Int.natAbs $d - 1)
    let d_half : Q(Nat) := q(Nat.div $real_d 2)
    let goalDeg : Q(Prop) := q($real_d = 2 * $d_half + 1)
    let (.mvar goalDeg_pf) ← Meta.mkFreshExprMVar (some goalDeg) | throwError "impossible 3"
    normNumFactorial goalDeg_pf

    let goal_l_nonneg : Q(Prop) := q(0 ≤ $lb)
    let (.mvar mv_l_nonneg) ← Meta.mkFreshExprMVar (some goal_l_nonneg) | throwError "impossible 3"
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := mv_l_nonneg)

    let ubBound : Q(Prop) := q($ub ≤ Real.pi)
    let (.mvar ubBound_pf) ← Meta.mkFreshExprMVar (some ubBound) | throwError "impossible 4"
    -- linarith [pi_gt_d20, pi_lt_d20] at ubBound_pf
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := ubBound_pf)

    let goalC : Q(Prop) := q($eval_c = TransFns.sinTaylor $real_d $c + ($c ^ ($real_d + 1) / ($real_d + 1).factorial))
    let (.mvar mvC) ← Meta.mkFreshExprMVar (some goalC) | throwError "impossible 2"
    normNumFactorial mvC

    let goalIf : Q(Prop) := q($c = if $ub < Real.pi/2 then $ub else if $lb < Real.pi/2 then Real.pi/2 else $lb)
    let (.mvar if_proof) ← Meta.mkFreshExprMVar (some goalIf) | throwError "impossible 4"
    let some [if1, if2] ← Meta.splitTarget? if_proof | throwError "split 1"
    let some [if3, if4] ← Meta.splitTarget? if2 | throwError "split 2"

    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if1)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if3)
    Mathlib.Tactic.Linarith.linarith false [.const `Real.pi_gt_d20 [], .const `Real.pi_lt_d20 []] (g := if4)

    let prop : Q(Prop) ← reconstructTerm pf.getResult
    let proof ← Meta.mkAppM ``TransFns.arithTransSineApproxAbovePosComp
      #[real_d, d_half, lb, ub, t, c, eval_c, .mvar goalDeg_pf, .mvar mv_l_nonneg, .mvar ubBound_pf, .mvar mvC, .mvar if_proof]
    addThm prop proof
  | _ => return none
where
normNumFactorial (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let simpTheorems ← simpTheorems.addDeclToUnfold `Nat.factorial
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  let remainingGoal? ← (Mathlib.Tactic.transformAtTarget (fun e ctx ↦ Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) e) "norm_num" (failIfUnchanged := false) mv).run ctx
  match remainingGoal? with
  | .some _ => throwError "[norm_num]: could not prove {← mv.getType}"
  | .none => pure ()
normNumAbs (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let simpTheorems ← simpTheorems.addDeclToUnfold `abs
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  let remainingGoal? ← (Mathlib.Tactic.transformAtTarget (fun e ctx ↦ Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) e) "norm_num" (failIfUnchanged := false) mv).run ctx
  match remainingGoal? with
  | .some _ => throwError "[norm_num]: could not prove {← mv.getType}"
  | .none => pure ()
