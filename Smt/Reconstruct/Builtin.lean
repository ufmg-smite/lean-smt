/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Builtin.Lemmas
import Smt.Reconstruct.Builtin.Rewrites
import Smt.Reconstruct

namespace Smt.Reconstruct.Builtin

open Lean Qq

@[smt_sort_reconstruct] def reconstructBuiltinSort : SortReconstructor := fun s => do match s.getKind with
  | .FUNCTION_SORT =>
    let mut curr : Q(Type) ← reconstructSort s.getFunctionCodomainSort
    for s in s.getFunctionDomainSorts do
      let t : Q(Type) ← reconstructSort s
      curr := q($t → $curr)
    return curr
  | _              => return none

def getFVarExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   => throwError "unknown free variable '{n}'"

def getFVarOrConstExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   =>
    let c ← getConstInfo n
    return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_term_reconstruct] def reconstructBuiltin : TermReconstructor := fun t => do match t.getKind with
  | .VARIABLE => getFVarExpr! (getVariableName t)
  | .CONSTANT => getFVarOrConstExpr! t.getSymbol
  | .ITE =>
    let α : Q(Type) ← reconstructSort t.getSort
    let c : Q(Prop) ← reconstructTerm t[0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let x : Q($α) ← reconstructTerm t[1]!
    let y : Q($α) ← reconstructTerm t[2]!
    return q(@ite $α $c $h $x $y)
  | .SKOLEM => match t.getSkolemId with
    | .PURIFY => reconstructTerm t.getSkolemIndices[0]!
    | _ => return none
  | _ => return none
where
  getVariableName (t : cvc5.Term) : Name :=
    if t.hasSymbol then t.getSymbol else Name.num `x t.getId

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | .ITE_TRUE_COND =>
    let α : Q(Type) ← reconstructSort pf.getArguments[1]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(ite True $x $y = $x) q(@Builtin.ite_true_cond $α $x $y)
  | .ITE_FALSE_COND =>
    let α : Q(Type) ← reconstructSort pf.getArguments[1]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(ite False $x $y = $y) q(@Builtin.ite_false_cond $α $x $y)
  | .ITE_NOT_COND =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite (¬$c) $x $y = ite $c $y $x) q(@Builtin.ite_not_cond $c $α $x $y $h)
  | .ITE_EQ_BRANCH =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x $x = $x) q(@Builtin.ite_eq_branch $c $α $x $h)
  | .ITE_THEN_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite $c $x $y) $z = ite $c $x $z) q(@Builtin.ite_then_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite $c $y $z) = ite $c $x $z) q(@Builtin.ite_else_lookahead $c $α $x $y $z $h)
  | .ITE_THEN_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite (¬$c) $x $y) $z = ite $c $y $z) q(@Builtin.ite_then_neg_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let α : Q(Type) ← reconstructSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite (¬$c) $y $z) = ite $c $x $y) q(@Builtin.ite_else_neg_lookahead $c $α $x $y $z $h)
  | _ => return none

@[smt_proof_reconstruct] def reconstructBuiltinProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .ASSUME =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]!
    match (← Meta.findLocalDeclWithType? p) with
    | none => throwError "no assumption of type\n\t{p}\nfound in local context"
    | some fv => return Expr.fvar fv
  | .SCOPE =>
    let mv ← getCurrGoal
    mv.withContext do
      let f := fun arg ps => do
        let p : Q(Prop) ← reconstructTerm arg
        return q($p :: $ps)
      let ps : Q(List Prop) ← pf.getArguments.foldrM f q([])
      let as ← pf.getArguments.mapM (fun _ => return Name.num `a (← incCount))
      let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
      let h₁ : Q(impliesN $ps $q) ← Meta.mkFreshExprMVar q(impliesN $ps $q)
      let (fvs, mv') ← h₁.mvarId!.introN pf.getArguments.size as.toList
      setCurrGoal mv'
      mv'.withContext do
        let h₂ : Q($q) ← withAssums (fvs.map Expr.fvar) (reconstructProof pf.getChildren[0]!)
        let mv'' ← getCurrGoal
        mv''.withContext (mv''.assignIfDefeq h₂)
      setCurrGoal mv
      addThm q(andN $ps → $q) q(Builtin.scopes $h₁)
  | .EVALUATE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    if (← reconstructTerm pf.getResult).getUsedConstants.any (isNoncomputable (← getEnv)) then
      return none
    -- TODO: handle case where a Prop is inside an expression
    if α.isProp then
      let p  : Q(Prop) ← reconstructTerm pf.getResult[0]!
      let p' : Q(Prop) ← reconstructTerm pf.getResult[1]!
      let h : Q(Decidable ($p = $p')) ← Meta.synthInstance q(Decidable ($p = $p'))
      addThm q($p = $p') (.app q(@of_decide_eq_true ($p = $p') $h) q(Eq.refl true))
    else
      let t  : Q($α) ← reconstructTerm pf.getResult[0]!
      let t' : Q($α) ← reconstructTerm pf.getResult[1]!
      addThm q($t = $t') q(Eq.refl $t)
  | .DSL_REWRITE => reconstructRewrite pf
  | .ITE_ELIM1 =>
    let c : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(@ite Prop $c $hc $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$c ∨ $p) q(Builtin.iteElim1 $h)
  | .ITE_ELIM2 =>
    let c : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(@ite Prop $c $hc $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q($c ∨ $q) q(Builtin.iteElim2 $h)
  | .NOT_ITE_ELIM1 =>
    let c : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q(¬@ite Prop $c $hc $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q(¬$c ∨ ¬$p) q(Builtin.notIteElim1 $hn)
  | .NOT_ITE_ELIM2 =>
    let c : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q(¬@ite Prop $c $hc $p $q) ← reconstructProof pf.getChildren[0]!
    addThm q($c ∨ ¬$q) q(Builtin.notIteElim2 $hn)
  | .CNF_ITE_POS1 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ ¬$c ∨ $p) q(@Builtin.cnfItePos1 $c $p $q $h)
  | .CNF_ITE_POS2 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ $c ∨ $q) q(@Builtin.cnfItePos2 $c $p $q $h)
  | .CNF_ITE_POS3 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ $p ∨ $q) q(@Builtin.cnfItePos3 $c $p $q $h)
  | .CNF_ITE_NEG1 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ ¬$c ∨ ¬$p) q(@Builtin.cnfIteNeg1 $c $p $q $h)
  | .CNF_ITE_NEG2 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ $c ∨ ¬$q) q(@Builtin.cnfIteNeg2 $c $p $q $h)
  | .CNF_ITE_NEG3 =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← reconstructTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ ¬$p ∨ ¬$q) q(@Builtin.cnfIteNeg3 $c $p $q $h)
  | .SKOLEM_INTRO =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let k : Q($α) ← reconstructTerm pf.getResult[0]!
    let t : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($k = $t) q(Eq.refl $t)
  | _ => return none

end Smt.Reconstruct.Builtin
