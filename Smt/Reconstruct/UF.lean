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

def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_sort_reconstruct] def reconstructUS : SortReconstructor := fun s => do match s.getKind! with
  | .UNINTERPRETED_SORT => getFVarOrConstExpr! s.getSymbol!
  | _ =>
    if s.isInstantiated then
      if let some ctor := s.getUninterpretedSortConstructor? then
        let base ← reconstructSort ctor
        let params ← s.getInstantiatedParameters!.mapM reconstructSort
        return some (mkAppN base params)
      else
        return none
    else
      return none

@[smt_term_reconstruct] def reconstructUF : TermReconstructor := fun t => do match t.getKind! with
  | .APPLY_UF =>
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := .app curr (← reconstructTerm t[i]!)
    return curr
  | .UNINTERPRETED_SORT_VALUE =>
    let some n := (← read).sortCard[t.getSort!]? | throwError "unknown sort {t.getSort!}"
    let s := t.toString
    let endPos := (s.rawEndPos - t.getSort!.toString).decreaseBy 2
    let endPos := s.pos! (if endPos.dec.get? s == some '|' then endPos.dec else endPos)
    let startPos := (endPos.revFind? (· != '_')).get!
    let i : Nat := (s.extract startPos endPos).toNat!
    if h : i < n then
      let i : Fin n := ⟨i, h⟩
      return toExpr i
    else
      throwError "index {i} is out of bounds for uninterpreted sort of cardinality {n}"
  | .SKOLEM =>
    match t.getSkolemId! with
    | .GROUND_TERM =>
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t.getSort!
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      return q(Classical.choice $hα)
    | _ => return none
  | _ => return none

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .EQ_REFL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    addThm q(($t = $t) = True) q(@UF.eq_refl $α $t)
  | .EQ_SYMM =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t = $s) = ($s = $t)) q(@UF.eq_symm $α $t $s)
  | .EQ_COND_DEQ =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    let r : Q($α) ← reconstructTerm pf.getArguments[3]!
    let h : Q(($s = $r) = False) ← reconstructProof pf.getChildren[0]!
    addThm q((($t = $s) = ($t = $r)) = (¬$t = $s ∧ ¬$t = $r)) q(@UF.eq_cond_deq $α $t $s $r $h)
  | .EQ_ITE_LIFT =>
    let c : Q(Bool) ← reconstructTerm pf.getArguments[1]!
    let hc : Q(Decidable $c) ← Meta.synthDecidableInstance q($c)
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[2]!
    let s : Q($α) ← reconstructTerm pf.getArguments[3]!
    let r : Q($α) ← reconstructTerm pf.getArguments[4]!
    addThm q((ite $c $t $s = $r) = (ite $c ($t = $r) ($s = $r))) q(@UF.eq_ite_lift $α $c $hc $t $s $r)
  | .DISTINCT_BINARY_ELIM =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[1]!
    let s : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(($t ≠ $s) = ¬($t = $s)) q(@UF.distinct_binary_elim $α $t $s)
  | _ => return none

@[smt_proof_reconstruct] def reconstructUFProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .REFL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]!.getSort!
    let a : Q($α) ← reconstructTerm pf.getArguments[0]!
    addThm q($a = $a) q(Eq.refl $a)
  | .SYMM =>
    if pf.getResult.getKind! == .EQUAL then
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort!
      let a : Q($α) ← reconstructTerm pf.getResult[1]!
      let b : Q($α) ← reconstructTerm pf.getResult[0]!
      let h : Q($a = $b) ← reconstructProof pf.getChildren[0]!
      addThm q($b = $a) q(Eq.symm $h)
    else
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]![0]!.getSort!
      let a : Q($α) ← reconstructTerm pf.getResult[0]![1]!
      let b : Q($α) ← reconstructTerm pf.getResult[0]![0]!
      let h : Q($a ≠ $b) ← reconstructProof pf.getChildren[0]!
      addThm q($b ≠ $a) q(Ne.symm $h)
  | .TRANS =>
    let cpfs := pf.getChildren
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort cpfs[0]!.getResult[0]!.getSort!
    let a : Q($α) ← reconstructTerm cpfs[0]!.getResult[0]!
    let mut curr ← reconstructProof cpfs[0]!
    for i in [1:cpfs.size] do
      let b : Q($α) ← reconstructTerm cpfs[i]!.getResult[0]!
      let c : Q($α) ← reconstructTerm cpfs[i]!.getResult[1]!
      let hab : Q($a = $b) := curr
      let hbc : Q($b = $c) ← reconstructProof cpfs[i]!
      curr := q(Eq.trans $hab $hbc)
    addThm (← reconstructTerm pf.getResult) curr
  | .CONG =>
    let k := pf.getResult[0]!.getKind!
    if k == .FORALL || k == .EXISTS || k == .WITNESS || k == .LAMBDA || k == .SET_COMPREHENSION then
      return none
    let mut assums ← pf.getChildren.mapM reconstructProof
    addTac (← reconstructTerm pf.getResult) (smtCongr · assums)
  | .NARY_CONG =>
    let mut assums ← pf.getChildren.mapM reconstructProof
    addTac (← reconstructTerm pf.getResult) (smtCongr · assums)
  | .HO_CONG =>
    let f ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let g ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let hfg ← reconstructProof pf.getChildren[0]!
    let hs := pf.getChildren[1:]
    let buildProof := fun (f₁, f₂, h₁) cpf => do
      let some (α, β) := (← Meta.inferType f₁).arrow? | throwError "[ho_congr]: expected function type"
      let .sort u ← Meta.inferType α | throwError "[ho_congr]: expected the type of {α} to be a sort"
      let .sort v ← Meta.inferType β | throwError "[ho_congr]: expected the type of {β} to be a sort"
      let α : Q(Sort u) ← pure α
      let β : Q(Sort v) ← pure β
      let a₁ : Q($α) ← reconstructTerm cpf.getResult[0]!
      let a₂ : Q($α) ← reconstructTerm cpf.getResult[1]!
      let f₁ : Q($α → $β) ← pure f₁
      let f₂ : Q($α → $β) ← pure f₂
      let h₁ : Q($f₁ = $f₂) ← pure h₁
      let h₂ : Q($a₁ = $a₂) ← reconstructProof cpf
      return (q($f₁ $a₁), q($f₂ $a₂), q(congr $h₁ $h₂))
    let (_, _, h) ← hs.foldlM buildProof (f, g, hfg)
    addThm (← reconstructTerm pf.getResult) h
  | _ => return none

end Smt.Reconstruct.UF
