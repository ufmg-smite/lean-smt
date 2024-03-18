/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.UF.Congruence
import Smt.Reconstruct.UF.Rewrites

namespace Smt.Reconstruct.UF

open Lean Qq

def getFVarOrConstExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   =>
    let c ← getConstInfo n
    return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_sort_reconstruct] def reconstructUS : SortReconstructor := fun s => do match s.getKind with
  | .INTERNAL_SORT_KIND
  | .UNINTERPRETED_SORT => getFVarOrConstExpr! s.getSymbol
  | _             => return none

@[smt_term_reconstruct] def reconstructUF : TermReconstructor := fun t => do match t.getKind with
  | .EQUAL =>
    let α : Q(Type) ← reconstructSort t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x = $y)
  | .DISTINCT =>
    let α : Q(Type) ← reconstructSort t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x ≠ $y)
  | .APPLY_UF =>
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := .app curr (← reconstructTerm t[i]!)
    return curr
  | _ => return none

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match cvc5.RewriteRule.fromNat! pf.getArguments[0]!.getIntegerValue.toNat with
  | .EQ_REFL =>
    let α : Q(Type) ← reconstructSort pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t = $t) = True) q(@UF.eq_refl $α $t)
  | .EQ_SYMM =>
    let α : Q(Type) ← reconstructSort pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t = $s) = ($s = $t)) q(@UF.eq_symm $α $t $s)
  | .DISTINCT_BINARY_ELIM =>
    let α : Q(Type) ← reconstructSort pf.getArguments[1]!.getSort
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≠ $s) = ¬($t = $s)) q(@UF.distinct_binary_elim $α $t $s)
  | _ => return none

@[smt_proof_reconstruct] def reconstructUFProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .REFL =>
    let α : Q(Type) ← reconstructSort pf.getArguments[0]!.getSort
    let a : Q($α) ← reconstructTerm pf.getArguments[0]!
    addThm q($a = $a) q(Eq.refl $a)
  | .SYMM =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let a : Q($α) ← reconstructTerm pf.getResult[1]!
    let b : Q($α) ← reconstructTerm pf.getResult[0]!
    if pf.getResult.getKind == .EQUAL then
      let h : Q($a = $b) ← reconstructProof pf.getChildren[0]!
      addThm q($b = $a) q(Eq.symm $h)
    else
      let h : Q($a ≠ $b) ← reconstructProof pf.getChildren[0]!
      addThm q($b ≠ $a) q(Ne.symm $h)
  | .TRANS =>
    let cpfs := pf.getChildren
    let α : Q(Type) ← reconstructSort cpfs[0]!.getResult[0]!.getSort
    let a : Q($α) ← reconstructTerm cpfs[0]!.getResult[0]!
    let mut curr ← reconstructProof cpfs[0]!
    for i in [1:cpfs.size] do
      let b : Q($α) ← reconstructTerm cpfs[i]!.getResult[0]!
      let c : Q($α) ← reconstructTerm cpfs[i]!.getResult[1]!
      let hab : Q($a = $b) := curr
      let hbc : Q($b = $c) ← reconstructProof cpfs[i]!
      curr ← addThm q($a = $c) q(Eq.trans $hab $hbc)
    return curr
  | .CONG =>
    let k := pf.getResult[0]!.getKind
    if k == .FORALL || k == .EXISTS || k == .WITNESS || k == .LAMBDA || k == .SET_COMPREHENSION then
      return none
    let mut assums ← pf.getChildren.mapM reconstructProof
    addTac (← reconstructTerm pf.getResult) (smtCongr · assums)
  | .NARY_CONG =>
    let mut assums ← pf.getChildren.mapM reconstructProof
    addTac (← reconstructTerm pf.getResult) (smtCongr · assums)
  | _ => return none

end Smt.Reconstruct.UF
