/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Builtin.AC
import Smt.Reconstruct.Builtin.Lemmas
import Smt.Reconstruct.Builtin.Rewrites
import Smt.Reconstruct.Builtin.Tactic

namespace Smt.Reconstruct.Builtin

open Lean Qq

@[smt_sort_reconstruct] def reconstructBuiltinSort : SortReconstructor := fun s => do match s.getKind with
  | .FUNCTION_SORT =>
    let ct ← reconstructSort s.getFunctionCodomainSort!
    let f := fun s a => do
      let t ← reconstructSort s
      return .forallE .anonymous t a .default
    let t ← s.getFunctionDomainSorts!.foldrM f ct
    return t
  | _              => return none

def getFVarExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   => throwError "unknown free variable '{n}'"

def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

def buildDistinct (u : Level) (α : Q(Sort u)) (xs : List Q($α)) : Q(Prop) :=
  go xs
where
  go : List Q($α) → Q(Prop)
  | [] => q(True)
  | [_] => q(True)
  | [x, y] => q($x ≠ $y)
  | x :: ys => ys.foldr (fun y ys => q($x ≠ $y ∧ $ys)) (go ys)

@[smt_term_reconstruct] def reconstructBuiltin : TermReconstructor := fun t => do match t.getKind with
  | .VARIABLE => getFVarExpr! (getVariableName t)
  | .CONSTANT => getFVarOrConstExpr! t.getSymbol!
  | .EQUAL =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t[0]!.getSort
    let x : Q($α) ← reconstructTerm t[0]!
    let y : Q($α) ← reconstructTerm t[1]!
    return q($x = $y)
  | .DISTINCT =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t[0]!.getSort
    let xs ← t.getChildren.mapM reconstructTerm
    return buildDistinct u α xs.toList
  | .ITE =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort t.getSort
    let c : Q(Prop) ← reconstructTerm t[0]!
    let oh : Option Q(Decidable $c) ← Meta.synthInstance? q(Decidable $c)
    let h : Q(Decidable $c) := oh.getD q(Classical.propDecidable $c)
    let x : Q($α) ← reconstructTerm t[1]!
    let y : Q($α) ← reconstructTerm t[2]!
    return q(@ite $α $c $h $x $y)
  | .SKOLEM => match t.getSkolemId! with
    | .PURIFY => reconstructTerm t.getSkolemIndices![0]!
    | _ => return none
  | _ => return none
where
  getVariableName (t : cvc5.Term) : Name :=
    if t.hasSymbol then
      if t.getSymbol!.toName == .anonymous then
        Name.mkSimple t.getSymbol!
      else
        t.getSymbol!.toName
    else Name.num `x t.getId

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .DISTINCT_ELIM =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .ITE_TRUE_COND =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(ite True $x $y = $x) q(@Builtin.ite_true_cond $α $x $y)
  | .ITE_FALSE_COND =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[1]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[1]!
    let y : Q($α) ← reconstructTerm pf.getArguments[2]!
    addThm q(ite False $x $y = $y) q(@Builtin.ite_false_cond $α $x $y)
  | .ITE_NOT_COND =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite (¬$c) $x $y = ite $c $y $x) q(@Builtin.ite_not_cond $c $α $x $y $h)
  | .ITE_EQ_BRANCH =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x $x = $x) q(@Builtin.ite_eq_branch $c $α $x $h)
  | .ITE_THEN_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite $c $x $y) $z = ite $c $x $z) q(@Builtin.ite_then_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite $c $y $z) = ite $c $x $z) q(@Builtin.ite_else_lookahead $c $α $x $y $z $h)
  | .ITE_THEN_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite (¬$c) $x $y) $z = ite $c $y $z) q(@Builtin.ite_then_neg_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← reconstructTerm pf.getArguments[1]!
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[2]!.getSort
    let x : Q($α) ← reconstructTerm pf.getArguments[2]!
    let y : Q($α) ← reconstructTerm pf.getArguments[3]!
    let z : Q($α) ← reconstructTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite (¬$c) $y $z) = ite $c $x $y) q(@Builtin.ite_else_neg_lookahead $c $α $x $y $z $h)
  | _ => return none

@[smt_proof_reconstruct] def reconstructBuiltinProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .ASSUME =>
    let p : Q(Prop) ← reconstructTerm pf.getArguments[0]!
    match (← findAssumWithType? p) with
    | none   => throwError "no assumption of type\n\t{p}\nfound in local context"
    | some a => return a
  | .SCOPE =>
    let f := fun arg ps => do
      let p : Q(Prop) ← reconstructTerm arg
      return q($p :: $ps)
    let ps : Q(List Prop) ← pf.getArguments.foldrM f q([])
    let as ← pf.getArguments.mapM (fun _ => return Name.num `a (← incCount))
    let q : Q(Prop) ← reconstructTerm pf.getChildren[0]!.getResult
    let h₁ : Q(impliesN $ps $q) ← Meta.mkFreshExprMVar q(impliesN $ps $q)
    let (fvs, mv) ← h₁.mvarId!.introN as.size as.toList
    withNewProofCache $ mv.withContext do
      let h₂ : Q($q) ← withAssums (fvs.map Expr.fvar) (reconstructProof pf.getChildren[0]!)
      mv.assign h₂
    addThm q(andN $ps → $q) q(Builtin.scopes $h₁)
  | .EVALUATE =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    if pf.getResult[0]! == pf.getResult[1]! then
      addThm q($t = $t') q(Eq.refl $t)
    else
      let hp : Q(Decidable ($t = $t')) ← Meta.synthInstance q(Decidable ($t = $t'))
      if hp.getUsedConstants.any (isNoncomputable (← getEnv)) then
        return none
      if ← useNative then
        addThm q($t = $t') (← nativeDecide q($t = $t') hp)
      else
        addThm q($t = $t') (← decide q($t = $t') hp)
  | .ACI_NORM =>
    addTac (← reconstructTerm pf.getResult) Meta.AC.rewriteUnnormalizedTop
  | .ABSORB =>
    let e ← reconstructTerm pf.getResult[0]!
    let z ← reconstructTerm pf.getResult[1]!
    let op := e.appFn!.appFn!
    let tac := if ← useNative then nativeAbsorb else absorb
    addTac (← reconstructTerm pf.getResult) (tac · z op)
  | .ENCODE_EQ_INTRO =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let x : Q($α) ← reconstructTerm pf.getResult[0]!
    let y : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($x = $y) q(Eq.refl $y)
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
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
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let k : Q($α) ← reconstructTerm pf.getResult[0]!
    let t : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($k = $t) q(Eq.refl $t)
  | _ => return none
where
  decide (p : Q(Prop)) (hp : Q(Decidable $p)) : MetaM Q($p) := do
    return .app q(@of_decide_eq_true $p $hp) q(Eq.refl true)
  nativeDecide (p : Q(Prop)) (hp : Q(Decidable $p)) : MetaM Q($p) := do
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxDeclName baseName
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

end Smt.Reconstruct.Builtin
