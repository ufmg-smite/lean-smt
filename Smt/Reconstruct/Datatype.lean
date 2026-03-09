/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Smt.Reconstruct

namespace Smt.Reconstruct.Datatype

open Lean Meta Qq

-- Strip SMT-LIB2 pipe quoting (|name|) from a symbol if present.
private def stripSMTPipes (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" then s.drop 1 |>.dropRight 1 else s

private def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

@[smt_sort_reconstruct] def reconstructDatatypeSort : SortReconstructor := fun s => do
  match s.getKind! with
  | .DATATYPE_SORT => getFVarOrConstExpr! s.getDatatype!.getName!
  | _ => return none

@[smt_term_reconstruct] def reconstructDatatypeTerm : TermReconstructor := fun t => do
  match t.getKind! with
  | .APPLY_CONSTRUCTOR =>
    -- t[0]! is the constructor symbol. It has INTERNAL_KIND in cvc5 (even for non-zero-arity),
    -- so we look it up by name instead of calling reconstructTerm recursively.
    -- toString may include SMT-LIB pipe escaping (e.g., "|mynat'.succ|"), so strip it.
    let mut curr ← getFVarOrConstExpr! (stripSMTPipes t[0]!.toString)
    for i in [1:t.getNumChildren] do
      curr := .app curr (← reconstructTerm t[i]!)
    return curr
  | _ => return none

/-- Build a Lean proof of `(t = s) = False` where `t` and `s` are
distinct constructors of the same inductive type. Uses the `noConfusion`
principle that Lean auto-generates for every inductive type. -/
private def proveConsClash (t s : Expr) : MetaM Expr := do
  let α ← inferType t
  let .const αName _ := α.getAppFn
    | throwError "Smt.Reconstruct.Datatype: expected inductive type, got {α}"
  let ncName := αName ++ `noConfusion
  let heq ← mkEq t s
  -- Forward: (t = s) → False  via noConfusion with motive False
  let fwd ← withLocalDeclD `h heq fun h => do
    let nc ← mkAppOptM ncName #[some (mkConst ``False), some t, some s, some h]
    mkLambdaFVars #[h] nc
  -- Backward: False → (t = s)  via False.elim
  let bwd ← withLocalDeclD `h (mkConst ``False) fun h => do
    let fe ← mkAppOptM ``False.elim #[some heq, some h]
    mkLambdaFVars #[h] fe
  let iff_pf ← mkAppM ``Iff.intro #[fwd, bwd]
  mkAppM ``propext #[iff_pf]

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .MACRO_DT_CONS_EQ
  | .DT_CONS_EQ_CLASH =>
    let result := pf.getResult
    -- Only handle the "clash" case: (t = s) = false (distinct constructors)
    if result[1]!.getKind! == .CONST_BOOLEAN && !result[1]!.getBooleanValue! then
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort result[0]![0]!.getSort!
      let t : Q($α) ← reconstructTerm result[0]![0]!
      let s : Q($α) ← reconstructTerm result[0]![1]!
      addTac q(($t = $s) = False) fun mv => do
        let proof ← mv.withContext (proveConsClash t s)
        mv.assign proof
    else
      return none
  | _ => return none

/-- Build a Lean proof of `¬(t = s)` where `t` and `s` are distinct constructors.
Uses the `noConfusion` principle: `fun h : t = s => noConfusion False t s h`. -/
private def proveDistinctValues (t s : Expr) : MetaM Expr := do
  let α ← inferType t
  let .const αName _ := α.getAppFn
    | throwError "Smt.Reconstruct.Datatype: expected inductive type, got {α}"
  let ncName := αName ++ `noConfusion
  let heq ← mkEq t s
  withLocalDeclD `h heq fun h => do
    let nc ← mkAppOptM ncName #[some (mkConst ``False), some t, some s, some h]
    mkLambdaFVars #[h] nc

@[smt_proof_reconstruct] def reconstructDatatypeProof : ProofReconstructor := fun pf => do
  match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .DISTINCT_VALUES =>
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getArguments[0]!.getSort!
    let t : Q($α) ← reconstructTerm pf.getArguments[0]!
    let s : Q($α) ← reconstructTerm pf.getArguments[1]!
    addTac q($t ≠ $s) fun mv => do
      let proof ← mv.withContext (proveDistinctValues t s)
      mv.assign proof
  | _ => return none

end Smt.Reconstruct.Datatype
