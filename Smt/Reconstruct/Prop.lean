/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct.Prop.Factor
import Smt.Reconstruct.Prop.Lemmas
import Smt.Reconstruct.Prop.LiftOrNToImp
import Smt.Reconstruct.Prop.LiftOrNToNeg
import Smt.Reconstruct.Prop.PermutateOr
import Smt.Reconstruct.Prop.Pull
import Smt.Reconstruct.Prop.Resolution
import Smt.Reconstruct.Prop.Rewrites
import Smt.Reconstruct
import Smt.Reconstruct.Rewrite

namespace Smt.Reconstruct.Prop

open Lean Qq

@[smt_sort_reconstruct] def reconstructSort : SortReconstructor := fun s => do match s.getKind with
  | .BOOLEAN_SORT => return q(Prop)
  | _             => return none

@[smt_term_reconstruct] def reconstructProp : TermReconstructor := fun t => do match t.getKind with
  | .CONST_BOOLEAN => return if t.getBooleanValue then q(True) else q(False)
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

def reconstructRewrite (pf : cvc5.Proof) (cpfs : Array Expr) : ReconstructM (Option Expr) := do
  match cvc5.RewriteRule.fromNat! pf.getArguments[0]!.getIntegerValue.toNat with
  | .BOOL_DOUBLE_NOT_ELIM =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    addThm q((¬¬$p) = $p) q(@Prop.bool_double_not_elim $p)
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
  -- | .BOOL_OR_TRUE =>
  --   let args ← reconstructArgs pf.getArguments
  --   addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_true) args)
  | .BOOL_OR_FALSE =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_false) args)
  | .BOOL_OR_FLATTEN =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_flatten) args)
  | .BOOL_OR_DUP =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_dup) args)
  | .BOOL_AND_TRUE =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_true) args)
  -- | .BOOL_AND_FALSE =>
  --   let args ← reconstructArgs pf.getArguments[1:]
  --   addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_false) args)
  | .BOOL_AND_FLATTEN =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_flatten) args)
  | .BOOL_AND_DUP =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_dup) args)
  | .BOOL_AND_CONF =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_conf) args)
  | .BOOL_OR_TAUT =>
    let args ← reconstructArgs pf.getArguments[1:]
    addTac (← reconstructTerm pf.getResult) (Tactic.smtRw · q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_taut) args)
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
    addThm q(XOr $p $q = ¬($p = $q)) q(@Prop.bool_xor_elim $p $q)
  | .ITE_NEG_BRANCH =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[3]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let h : Q($p = ¬$q) := cpfs[0]!
    addThm q(ite $c $p $q = ($c = $p)) q(@Prop.ite_neg_branch $c $p $q $hc $h)
  | .ITE_THEN_TRUE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c True $p = ($c ∨ $p)) q(@Prop.ite_then_true $c $p $h)
  | .ITE_ELSE_FALSE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p False = ($c ∧ $p)) q(@Prop.ite_else_false $c $p $h)
  | .ITE_THEN_FALSE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c False $p = (¬$c ∧ $p)) q(@Prop.ite_then_false $c $p $h)
  | .ITE_ELSE_TRUE =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let p : Q(Prop) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p True = (¬$c ∨ $p)) q(@Prop.ite_else_true $c $p $h)
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

def getResolutionResult (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) : Array cvc5.Term := Id.run do
  let l₁ := if pol.getBooleanValue then l else l.not
  let l₂ := if pol.getBooleanValue then l.not else l
  let mut ls := #[]
  for li in c₁ do
    if li != l₁ then
      ls := ls.push li
  for li in c₂ do
    if li != l₂ then
      ls := ls.push li
  return ls

def reconstructResolution (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) (p₁ p₂ : Expr) : ReconstructM Expr := do
  let f := if pol.getBooleanValue == true then r₀ else r₁
  addTac (← rightAssocOp q(Or) (getResolutionResult c₁ c₂ pol l)) (f · p₁ p₂ (← reconstructTerm l) (some (c₁.size - 1)) (some (c₂.size - 1)))
where
  rightAssocOp (op : Expr) (ts : Array cvc5.Term) : ReconstructM Expr := do
    if ts.isEmpty then
      return q(False)
    let mut curr ← reconstructTerm ts[ts.size - 1]!
    for i in [1:ts.size] do
      curr := mkApp2 op (← reconstructTerm ts[ts.size - i - 1]!) curr
    return curr

def clausify (c : cvc5.Term) : Array cvc5.Term := Id.run do
  if c.getKind != .OR then
    return #[c]
  let mut cs := #[]
  for cc in c do
    cs := cs.push cc
  return cs

def reconstructChainResolution (cs as : Array cvc5.Term) (ps : Array Expr) : ReconstructM Expr := do
  let mut cc := clausify cs[0]!
  let mut cp := ps[0]!
  for i in [1:cs.size] do
    let pol := as[0]![i - 1]!
    let l := as[1]![i - 1]!
    cp ← reconstructResolution cc (clausify cs[i]!) pol l cp ps[i]!
    cc := getResolutionResult cc (clausify cs[i]!) pol l
  return cp

@[smt_proof_reconstruct] def reconstructPropProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf (← pf.getChildren.mapM reconstructProof)
  | .RESOLUTION =>
    let c₁ := clausify pf.getChildren[0]!.getResult
    let c₂ := clausify pf.getChildren[1]!.getResult
    let p₁ ← reconstructProof pf.getChildren[0]!
    let p₂ ← reconstructProof pf.getChildren[1]!
    reconstructResolution c₁ c₂ pf.getArguments[0]! pf.getArguments[1]! p₁ p₂
  | .CHAIN_RESOLUTION =>
    let cs := pf.getChildren.map (·.getResult)
    let as := pf.getArguments
    let ps ← pf.getChildren.mapM reconstructProof
    reconstructChainResolution cs as ps
  | .FACTORING =>
    -- as an argument we pass whether the suffix of the factoring clause is a
    -- singleton *repeated* literal. This is marked by a number as in
    -- resolution.
    let children := pf.getChildren
    let lastPremiseLit := children[0]!.getResult[children[0]!.getResult.getNumChildren - 1]!
    let resOriginal := pf.getResult
    -- For the last premise literal to be a singleton repeated literal, either
    -- it is equal to the result (in which case the premise was just n
    -- occurrences of it), or the end of the original clause is different from
    -- the end of the resulting one. In principle we'd need to add the
    -- singleton information only for OR nodes, so we could avoid this test if
    -- the result is not an OR node. However given the presence of
    -- purification boolean variables which can stand for OR nodes (and could
    -- thus be ambiguous in the final step, with the purification remove), we
    -- do the general test.
    let singleton := if lastPremiseLit == resOriginal || (resOriginal.getKind == .OR && lastPremiseLit != resOriginal[resOriginal.getNumChildren - 1]!)
      then some (children[0]!.getResult.getNumChildren - 1) else none;
    addTac (← reconstructTerm pf.getResult) (factor · (← reconstructProof children[0]!) singleton)
  | .REORDERING =>
    let children := pf.getChildren
    let size := pf.getResult.getNumChildren
    let lastPremiseLit := children[0]!.getResult[size - 1]!
    -- none if tail of the clause is not an OR (i.e., it cannot be a singleton)
    let singleton := if lastPremiseLit.getKind == .OR then some (size - 1) else none
    -- for each literal in the resulting clause, get its position in the premise
    let mut pos := #[]
    for resLit in pf.getResult do
      for i in [:size] do
        if children[0]!.getResult[i]! == resLit then
          pos := pos.push i
    -- turn conclusion into clause
    addTac (← reconstructTerm pf.getResult) (reorder · (← reconstructProof children[0]!) pos singleton)
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
    let hnp : Q(¬$p) ← reconstructProof pf.getChildren[0]!
    addThm q(False) q(Prop.contradiction $hp $hnp)
  | .AND_ELIM =>
    addTac (← reconstructTerm pf.getResult) (andElim · (← reconstructProof pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
  | .AND_INTRO =>
    let cpfs := pf.getChildren
    let q : Q(Prop) ← reconstructTerm cpfs.back.getResult
    let hq : Q($q) ← reconstructProof cpfs.back
    let f := fun pf ⟨q, hq⟩ => do
      let p : Q(Prop) ← reconstructTerm pf.getResult
      let hp : Q($p) ← reconstructProof pf
      let hq ← addThm q($p ∧ $q) q(And.intro $hp $hq)
      let q := q($p ∧ $q)
      return ⟨q, hq⟩
    let ⟨_, hq⟩ ← cpfs.pop.foldrM f (⟨q, hq⟩ : Σ q : Q(Prop), Q($q))
    return hq
  | .NOT_OR_ELIM =>
    addTac (← reconstructTerm pf.getResult) (notOrElim · (← reconstructProof pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
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
    let i : Nat := pf.getArguments[1]!.getIntegerValue.toNat
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
    addThm (← reconstructTerm pf.getResult) q(Prop.cnfAndNeg $ps)
  | .CNF_OR_POS =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← reconstructTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← reconstructTerm pf.getResult) q(Prop.cnfOrPos $ps)
  | .CNF_OR_NEG =>
    let cnf := pf.getArguments[0]!
    let i : Nat := pf.getArguments[1]!.getIntegerValue.toNat
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
