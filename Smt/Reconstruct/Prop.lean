/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Builtin.AC
import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct.Prop.Lemmas
import Smt.Reconstruct.Prop.Rewrites

namespace Smt.Reconstruct.Prop

open Lean Qq

@[smt_sort_reconstruct] def reconstructPropSort : SortReconstructor := fun s => do match s.getKind with
  | .BOOLEAN_SORT => return q(Prop)
  | _             => return none

@[smt_term_reconstruct] def reconstructProp : TermReconstructor := fun t => do match t.getKind with
  | .CONST_BOOLEAN => return if t.getBooleanValue! then q(True) else q(False)
  | .NOT =>
    let b : Q(Prop) ← reconstructTerm t[0]!
    return q(¬$b)
  | .IMPLIES =>
    let mut curr : Q(Prop) ← reconstructTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let p : Q(Prop) ← reconstructTerm t[t.getNumChildren - i - 1]!
      curr := q($p → $curr)
    return curr
  | .AND => rightAssocOp q(And) t
  | .OR => rightAssocOp q(Or) t
  | .XOR => rightAssocOp q(XOr) t
  | _ => return none
where
  rightAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op (← reconstructTerm t[t.getNumChildren - i - 1]!) curr
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .BOOL_DOUBLE_NOT_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q((¬¬$p) = $p) q(@Prop.bool_double_not_elim $p)
  | .BOOL_NOT_TRUE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hpf : Q($p = False) ← reconstructProof pf.getChildren[0]!
    addThm q((¬$p) = True) q(@Prop.bool_not_true $p $hpf)
  | .BOOL_NOT_FALSE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let hpt : Q($p = True) ← reconstructProof pf.getChildren[0]!
    addThm q((¬$p) = False) q(@Prop.bool_not_false $p $hpt)
  | .BOOL_EQ_TRUE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(($p = True) = $p) q(@Prop.bool_eq_true $p)
  | .BOOL_EQ_FALSE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(($p = False) = ¬$p) q(@Prop.bool_eq_false $p)
  | .BOOL_EQ_NREFL =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(($p = ¬$p) = False) q(@Prop.bool_eq_nrefl $p)
  | .BOOL_IMPL_FALSE1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(($p → False) = ¬$p) q(@Prop.bool_impl_false1 $p)
  | .BOOL_IMPL_FALSE2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q((False → $p) = True) q(@Prop.bool_impl_false2 $p)
  | .BOOL_IMPL_TRUE1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(($p → True) = True) q(@Prop.bool_impl_true1 $p)
  | .BOOL_IMPL_TRUE2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q((True → $p) = $p) q(@Prop.bool_impl_true2 $p)
  | .BOOL_IMPL_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q(($p → $q) = orN [¬$p, $q]) q(@Prop.bool_impl_elim $p $q)
  | .BOOL_DUAL_IMPL_EQ =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q(andN [$p → $q, $q → $p] = ($p = $q)) q(@Prop.bool_dual_impl_eq $p $q)
  | .BOOL_OR_FLATTEN =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let b₁ : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let b₂ : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[5]!.getChildren
    addThm q(orN ($xs ++ orN ($b₁ :: $b₂ :: $ys) :: $zs) = orN ($xs ++ $b₁ :: $b₂ :: ($ys ++ $zs)))
           q(@Prop.bool_or_flatten $xs $b₁ $b₂ $ys $zs)
  | .BOOL_AND_FLATTEN =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let b₁ : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let b₂ : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[5]!.getChildren
    addThm q(andN ($xs ++ andN ($b₁ :: $b₂ :: $ys) :: $zs) = andN ($xs ++ $b₁ :: $b₂ :: ($ys ++ $zs)))
           q(@Prop.bool_and_flatten $xs $b₁ $b₂ $ys $zs)
  | .BOOL_AND_CONF =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(andN ($xs ++ $w :: ($ys ++ (¬$w) :: $zs)) = False) q(@Prop.bool_and_conf $xs $w $ys $zs)
  | .BOOL_AND_CONF2 =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(andN ($xs ++ (¬$w) :: ($ys ++ $w :: $zs)) = False) q(@Prop.bool_and_conf2 $xs $w $ys $zs)
  | .BOOL_OR_TAUT =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(orN ($xs ++ $w :: ($ys ++ (¬$w) :: $zs)) = True) q(@Prop.bool_or_taut $xs $w $ys $zs)
  | .BOOL_OR_TAUT2 =>
    let xs : Q(List Prop) ← reconstructTerms pf.getArguments[1]!.getChildren
    let w : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[4]!.getChildren
    addThm q(orN ($xs ++ (¬$w) :: ($ys ++ $w :: $zs)) = True) q(@Prop.bool_or_taut2 $xs $w $ys $zs)
  | .BOOL_OR_DE_MORGAN =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    addThm q((¬orN ($p :: $q :: $zs)) = andN [¬$p, ¬orN ($q :: $zs)]) q(@Prop.bool_or_de_morgan $p $q $zs)
  | .BOOL_IMPLIES_DE_MORGAN =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬($p → $q)) = andN [$p, ¬$q]) q(@Prop.bool_implies_de_morgan $p $q)
  | .BOOL_AND_DE_MORGAN =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    addThm q((¬andN ($p :: $q :: $zs)) = orN [¬$p, ¬andN ($q :: $zs)]) q(@Prop.bool_and_de_morgan $p $q $zs)
  | .BOOL_OR_AND_DISTRIB =>
    let y₁ : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let y₂ : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let z₁ : Q(Prop) ← reconstructTerm pf.getArguments[4]!
    let zs : Q(List Prop) ← reconstructTerms pf.getArguments[5]!.getChildren
    addThm (← reconstructTerm pf.getResult) q(@Prop.bool_or_and_distrib $y₁ $y₂ $ys $z₁ $zs)
  | .BOOL_IMPLIES_OR_DISTRIB =>
    let y₁ : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let y₂ : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let ys : Q(List Prop) ← reconstructTerms pf.getArguments[3]!.getChildren
    let z : Q(Prop) ← reconstructTerm pf.getArguments[4]!
    addThm q((orN ($y₁ :: $y₂ :: $ys) → $z) = andN [$y₁ → $z, orN ($y₂ :: $ys) → $z])
           q(@Prop.bool_implies_or_distrib $y₁ $y₂ $ys $z)
  | .BOOL_XOR_REFL =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(XOr $p $p = False) q(@Prop.bool_xor_refl $p)
  | .BOOL_XOR_NREFL =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q((XOr $p ¬$p) = True) q(@Prop.bool_xor_nrefl $p)
  | .BOOL_XOR_FALSE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(XOr $p False = $p) q(@Prop.bool_xor_false $p)
  | .BOOL_XOR_TRUE =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q(XOr $p True = ¬$p) q(@Prop.bool_xor_true $p)
  | .BOOL_XOR_COMM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q(XOr $p $q = XOr $q $p) q(@Prop.bool_xor_comm $p $q)
  | .BOOL_XOR_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q(XOr $p $q = ((¬$p) = $q)) q(@Prop.bool_xor_elim $p $q)
  | .BOOL_NOT_XOR_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬XOr $p $q) = ($p = $q)) q(@Prop.bool_not_xor_elim $p $q)
  | .BOOL_NOT_EQ_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬$p = $q) = ((¬$p) = $q)) q(@Prop.bool_not_eq_elim1 $p $q)
  | .BOOL_NOT_EQ_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    addThm q((¬$p = $q) = ($p = (¬$q))) q(@Prop.bool_not_eq_elim2 $p $q)
  | .ITE_NEG_BRANCH =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let h : Q($p = ¬$q) ← reconstructProof pf.getChildren[0]!
    addThm q(ite $c $p $q = ($c = $p)) q(@Prop.ite_neg_branch $c $p $q $hc $h)
  | .ITE_THEN_TRUE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c True $p = orN [$c, $p]) q(@Prop.ite_then_true $c $p $h)
  | .ITE_ELSE_FALSE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p False = andN [$c, $p]) q(@Prop.ite_else_false $c $p $h)
  | .ITE_THEN_FALSE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c False $p = andN [¬$c, $p]) q(@Prop.ite_then_false $c $p $h)
  | .ITE_ELSE_TRUE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p True = orN [¬$c, $p]) q(@Prop.ite_else_true $c $p $h)
  | .ITE_THEN_LOOKAHEAD_SELF =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $c $p = ite $c True $p) q(@Prop.ite_then_lookahead_self $c $p $h)
  | .ITE_ELSE_LOOKAHEAD_SELF =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p $c = ite $c $p False) q(@Prop.ite_else_lookahead_self $c $p $h)
  | .ITE_THEN_LOOKAHEAD_NOT_SELF =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (¬$c) $p = ite $c False $p) q(@Prop.ite_then_lookahead_not_self $c $p $h)
  | .ITE_ELSE_LOOKAHEAD_NOT_SELF =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p (¬$c) = ite $c $p True) q(@Prop.ite_else_lookahead_not_self $c $p $h)
  | .ITE_EXPAND =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p $q = andN [orN [¬$c, $p], orN [$c, $q]]) q(@Prop.ite_expand $c $p $q $h)
  | .BOOL_NOT_ITE_ELIM =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q((¬ite $c $p $q) = ite $c (¬$p) (¬$q)) q(@Prop.bool_not_ite_elim $c $p $q $h)
  | _ => return none

def nary (k : cvc5.Kind) (c : cvc5.Term) : Array cvc5.Term := Id.run do
  if c.getKind != k then
    return #[c]
  let mut cs := #[]
  for cc in c do
    cs := cs.push cc
  return cs

def reclausify (c : Array cvc5.Term) (l : cvc5.Term) : Array cvc5.Term :=
  if c == nary .OR l then #[l] else c

def clausify (c l : cvc5.Term) : Array cvc5.Term :=
  reclausify (nary .OR c) l

def getResolutionResult (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) : Array cvc5.Term := Id.run do
  let l₁ := if pol.getBooleanValue! then l else l.not!
  let l₂ := if pol.getBooleanValue! then l.not! else l
  let mut ls := #[]
  for li in c₁ do
    if li != l₁ then
      ls := ls.push li
  for li in c₂ do
    if li != l₂ then
      ls := ls.push li
  return ls

def reconstructResolution (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) (hps hqs : Expr) : ReconstructM Expr := do
  let f t ps := do
    let p : Q(Prop) ← reconstructTerm t
    return q($p :: $ps)
  let ps : Q(List Prop) ← c₁.foldrM f q([])
  let qs : Q(List Prop) ← c₂.foldrM f q([])
  let hps : Q(orN $ps) ← pure hps
  let hqs : Q(orN $qs) ← pure hqs
  let (i?, j?) := if pol.getBooleanValue! then (c₁.indexOf? l, c₂.indexOf? l.not!) else (c₁.indexOf? l.not!, c₂.indexOf? l)
  if let (some ⟨i, _⟩, some ⟨j, _⟩) := (i?, j?) then
    let hi : Q($i < «$ps».length) := .app q(@of_decide_eq_true ($i < «$ps».length) _) q(Eq.refl true)
    let hj : Q($j < «$qs».length) := .app q(@of_decide_eq_true ($j < «$qs».length) _) q(Eq.refl true)
    let hij : Q($ps[$i] = ¬$qs[$j]) :=
      if pol.getBooleanValue! then .app q(Prop.eq_not_not) q($ps[$i])
      else .app q(@Eq.refl Prop) q($ps[$i])
    return q(Prop.orN_resolution $hps $hqs $hi $hj $hij)
  else
    return q(@Prop.orN_append_left $ps $qs $hps)
where
  rightAssocOp (op : Expr) (ts : Array cvc5.Term) : ReconstructM Expr := do
    if ts.isEmpty then
      return q(False)
    let mut curr ← reconstructTerm ts[ts.size - 1]!
    for i in [1:ts.size] do
      curr := mkApp2 op (← reconstructTerm ts[ts.size - i - 1]!) curr
    return curr

def reconstructChainResolution (cs as : Array cvc5.Term) (ps : Array Expr) : ReconstructM Expr := do
  let mut cc := nary .OR cs[0]!
  let mut cp := ps[0]!
  for i in [1:cs.size] do
    let pol := as[0]![i - 1]!
    let l := as[1]![i - 1]!
    cc := reclausify cc l
    cp ← reconstructResolution cc (clausify cs[i]! l) pol l cp ps[i]!
    cc := getResolutionResult cc (clausify cs[i]! l) pol l
  return cp

@[smt_proof_reconstruct] def reconstructPropProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .ITE_EQ =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]![1]!.getSort
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let x : Q($α) ← reconstructTerm pf.getArguments[0]![1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(ite $c ((ite $c $x $y) = $x) ((ite $c $x $y) = $y)) q(@Prop.ite_eq $α $c $hc $x $y)
  | .RESOLUTION =>
    let p := pf.getArguments[0]!
    let l := pf.getArguments[1]!
    let c₁ := clausify pf.getChildren[0]!.getResult l
    let c₂ := clausify pf.getChildren[1]!.getResult l
    let hps ← reconstructProof pf.getChildren[0]!
    let hqs ← reconstructProof pf.getChildren[1]!
    addThm (← reconstructTerm pf.getResult) (← reconstructResolution c₁ c₂ p l hps hqs)
  | .CHAIN_RESOLUTION =>
    let cs := pf.getChildren.map (·.getResult)
    let as := pf.getArguments
    let ps ← pf.getChildren.mapM reconstructProof
    addThm (← reconstructTerm pf.getResult) (← reconstructChainResolution cs as ps)
  | .FACTORING =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← reconstructTerm pf.getResult
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← Meta.mkFreshExprMVar q($p = $q)
    Meta.AC.rewriteUnnormalizedTop hpq.mvarId!
    addThm q($q) q(Prop.eqResolve $hp $hpq)
  | .REORDERING =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← reconstructTerm pf.getResult
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← Meta.mkFreshExprMVar q($p = $q)
    Meta.AC.rewriteUnnormalizedTop hpq.mvarId!
    addThm q($q) q(Prop.eqResolve $hp $hpq)
  | .SPLIT =>
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]!
    addThm q($q ∨ ¬$q) q(Classical.em $q)
  | .EQ_RESOLVE =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← reconstructTerm pf.getResult
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← reconstructProof pf.getChildren[1]!
    addThm q($q) q(Prop.eqResolve $hp $hpq)
  | .MODUS_PONENS =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← reconstructTerm pf.getResult
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    let hpq : Q($p → $q) ← reconstructProof pf.getChildren[1]!
    addThm q($q) q(Prop.modusPonens $hp $hpq)
  | .NOT_NOT_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getResult
    let hnnp : Q(¬¬$p) ← reconstructProof pf.getChildren[0]!
    addThm q($p) q(Prop.notNotElim $hnnp)
  | .CONTRA =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    let hnp : Q(¬$p) ← reconstructProof pf.getChildren[1]!
    addThm q(False) q(Prop.contradiction $hp $hnp)
  | .AND_ELIM =>
    let f t ps := do
      let p : Q(Prop) ← reconstructTerm t
      return q($p :: $ps)
    let ps : Q(List Prop) ← (nary .AND pf.getChildren[0]!.getResult).foldrM f q([])
    let i : Nat := pf.getArguments[0]!.getIntegerValue!.toNat
    let hi : Q($i < «$ps».length) := .app q(@of_decide_eq_true ($i < «$ps».length) _) q(Eq.refl true)
    let hps : Q(andN $ps) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructTerm pf.getResult) q(@Prop.and_elim _ $hps $i $hi)
  | .AND_INTRO =>
    let cpfs := pf.getChildren
    let q : Q(Prop) ← reconstructTerm cpfs.back!.getResult
    let hq : Q($q) ← reconstructProof cpfs.back!
    let f := fun pf ⟨q, hq⟩ => do
      let p : Q(Prop) ← reconstructTerm pf.getResult
      let hp : Q($p) ← reconstructProof pf
      return ⟨q($p ∧ $q), q(And.intro $hp $hq)⟩
    let ⟨q, hq⟩ ← cpfs.pop.foldrM f (⟨q, hq⟩ : Σ q : Q(Prop), Q($q))
    addThm q hq
  | .NOT_OR_ELIM =>
    let f t ps := do
      let p : Q(Prop) ← reconstructTerm t
      return q($p :: $ps)
    let ps : Q(List Prop) ← (nary .OR pf.getChildren[0]!.getResult[0]!).foldrM f q([])
    let i : Nat := pf.getArguments[0]!.getIntegerValue!.toNat
    let hi : Q($i < «$ps».length) := .app q(@of_decide_eq_true ($i < «$ps».length) _) q(Eq.refl true)
    let hnps : Q(¬orN $ps) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructTerm pf.getResult) q(@Prop.not_or_elim _ $hnps $i $hi)
  | .IMPLIES_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let hpq : Q($p → $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.impliesElim $hpq)
  | .NOT_IMPLIES_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let hnpq : Q(¬($p → $q)) ← reconstructProof pf.getChildren[0]!
    addThm q($p) q(Prop.notImplies1 $hnpq)
  | .NOT_IMPLIES_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let hnpq : Q(¬($p → $q)) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$q) q(Prop.notImplies2 $hnpq)
  | .EQUIV_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let hpq : Q($p = $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.equivElim1 $hpq)
  | .EQUIV_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]![0]!
    let hpq : Q($p = $q) ← reconstructProof pf.getChildren[0]!
    addThm q($p ∨ ¬$q) q(Prop.equivElim2 $hpq)
  | .NOT_EQUIV_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let hnpq : Q($p ≠ $q) ← reconstructProof pf.getChildren[0]!
    addThm q($p ∨ $q) q(Prop.notEquivElim1 $hnpq)
  | .NOT_EQUIV_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]![0]!
    let hnpq : Q($p ≠ $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p ∨ ¬$q) q(Prop.notEquivElim2 $hnpq)
  | .XOR_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let hpq : Q(XOr $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q($p ∨ $q) q(Prop.xorElim1 $hpq)
  | .XOR_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]![0]!
    let hpq : Q(XOr $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p ∨ ¬$q) q(Prop.xorElim2 $hpq)
  | .NOT_XOR_ELIM1 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]![0]!
    let hnpq : Q(¬XOr $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q($p ∨ ¬$q) q(Prop.notXorElim1 $hnpq)
  | .NOT_XOR_ELIM2 =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let hnpq : Q(¬XOr $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.notXorElim2 $hnpq)
  | .NOT_AND =>
    let fs := pf.getChildren[0]!.getResult[0]!
    let mut ps : Q(List Prop) := q([])
    let n := fs.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm fs[n - i - 1]!
      ps := q($p :: $ps)
    let hnps : Q(¬andN $ps) ← reconstructProof pf.getChildren[0]!
    addThm (← reconstructTerm pf.getResult) (.app q(Prop.notAnd $ps) hnps)
  | .CNF_AND_POS =>
    let cnf := pf.getArguments[0]!
    let i : Nat := pf.getArguments[1]!.getIntegerValue!.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← reconstructTerm pf.getResult) q(Prop.cnfAndPos $ps $i)
  | .CNF_AND_NEG =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← reconstructTerm pf.getResult) q(@Prop.cnfAndNeg $ps)
  | .CNF_OR_POS =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← reconstructTerm pf.getResult) q(@Prop.cnfOrPos $ps)
  | .CNF_OR_NEG =>
    let cnf := pf.getArguments[0]!
    let i : Nat := pf.getArguments[1]!.getIntegerValue!.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← reconstructTerm pf.getResult) q(Prop.cnfOrNeg $ps $i)
  | .CNF_IMPLIES_POS =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(¬($p → $q) ∨ ¬$p ∨ $q) q(@Prop.cnfImpliesPos $p $q)
  | .CNF_IMPLIES_NEG1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(($p → $q) ∨ $p) q(@Prop.cnfImpliesNeg1 $p $q)
  | .CNF_IMPLIES_NEG2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(($p → $q) ∨ ¬$q) q(@Prop.cnfImpliesNeg2 $p $q)
  | .CNF_EQUIV_POS1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q($p ≠ $q ∨ ¬$p ∨ $q) q(@Prop.cnfEquivPos1 $p $q)
  | .CNF_EQUIV_POS2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q($p ≠ $q ∨ $p ∨ ¬$q) q(@Prop.cnfEquivPos2 $p $q)
  | .CNF_EQUIV_NEG1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q($p = $q ∨ $p ∨ $q) q(@Prop.cnfEquivNeg1 $p $q)
  | .CNF_EQUIV_NEG2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q($p = $q ∨ ¬$p ∨ ¬$q) q(@Prop.cnfEquivNeg2 $p $q)
  | .CNF_XOR_POS1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(¬XOr $p $q ∨ $p ∨ $q) q(@Prop.cnfXorPos1 $p $q)
  | .CNF_XOR_POS2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(¬XOr $p $q ∨ ¬$p ∨ ¬$q) q(@Prop.cnfXorPos2 $p $q)
  | .CNF_XOR_NEG1 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(XOr $p $q ∨ ¬$p ∨ $q) q(@Prop.cnfXorNeg1 $p $q)
  | .CNF_XOR_NEG2 =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    addThm q(XOr $p $q ∨ $p ∨ ¬$q) q(@Prop.cnfXorNeg2 $p $q)
  | .TRUE_INTRO =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let hp : Q($p) ← reconstructProof pf.getChildren[0]!
    addThm q($p = True) q(Prop.trueIntro $hp)
  | .TRUE_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getResult
    let hp : Q($p = True) ← reconstructProof pf.getChildren[0]!
    addThm q($p) q(Prop.trueElim $hp)
  | .FALSE_INTRO =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let hnp : Q(¬$p) ← reconstructProof pf.getChildren[0]!
    addThm q($p = False) q(Prop.falseIntro $hnp)
  | .FALSE_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let hnp : Q($p = False) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$p) q(Prop.falseElim $hnp)
  | _ => return none

end Smt.Reconstruct.Prop
