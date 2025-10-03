/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

import Smt
import Smt.Real
import Aesop
import Qq

open Lean Meta Parser Elab Tactic Syntax Aesop Qq

-- The string representation and the actual expr of the premisses
abbrev Premises := List (Expr × Syntax)

def f (stx : Syntax) : BaseM (TSyntax `term) :=
  match stx with
  | `($t) => return t

def f' (stx : Syntax) : TacticM (TSyntax `term) :=
  match stx with
  | `($t) => return t

def smtSingleRuleTac (ps : Premises) (includeLCtx : Bool) : SingleRuleTac := fun input => do
  let preState ← saveState
  input.goal.withContext do

    let goal_copy := (← Meta.mkFreshExprMVar (← input.goal.getType)).mvarId!
    let V := (ps.map (fun p => p.1)).toArray
    try
      let res ← Smt.smt default goal_copy V
    catch e => logInfo "hi"
    finally logInfo "erro"
    let unsat_core : List String := []
    /- let unsat_core ← -/
    /-   match res with -/
    /-   | .unsat mvs uc => pure uc -/
    /-   | _ => throwError "[Smt.smt]: Got SAT from solver" -/

    /- let names := unsat_core.map (fun e => (ps.lookup e).get!) -/
    /- let namesT ← names.mapM f -/
    /- let idents ← namesT.mapM (fun i => `(Smt.Tactic.smtHintElem| $i:term)) -/
    let stx ←
      if includeLCtx && !unsat_core.isEmpty then
        `(tactic| smt [*])
      else if includeLCtx && unsat_core.isEmpty then
        `(tactic| smt [*])
      else if !includeLCtx && !unsat_core.isEmpty then
        `(tactic| smt [*])
      else -- if !includeLCtx && unsat_core.isEmpty
        `(tactic| smt [*])
    let tac := withoutRecover $ evalTactic stx
    let postGoals := (← Elab.Tactic.run input.goal tac |>.run').toArray
    let postState ← saveState
    let tacticBuilder : MetaM Script.Tactic := pure $ .unstructured ⟨stx⟩
    let step : Script.LazyStep := {
      preGoal := input.goal
      tacticBuilders := #[tacticBuilder]
      preState, postState, postGoals
    }
    let postGoals ← postGoals.mapM (mvarIdToSubgoal input.goal ·)
    return (postGoals, some #[step], some ⟨1.0⟩)

-- Example using the above function to integrate lean-smt into aesop

syntax (name := foo) "foo" ("[" term,* "]")? : tactic

def parseFoo : Syntax → TacticM (List (Expr × Syntax))
  | `(tactic| foo) => pure []
  | `(tactic| foo [ $[$ns],* ]) => do
      let exprs ← ns.toList.mapM (fun t => elabTerm t.raw none)
      return List.zip exprs ns.toList
  | _ => throwError "[foo]: unexpected syntax"

@[tactic foo]
def evalFoo : Tactic := fun stx => withMainContext do
  let names : List (Expr × Syntax) ← parseFoo stx
  let ruleTacVal ← mkAppM `smtSingleRuleTac #[q($names), q(false)]
  let ruleTacType := mkConst `Aesop.SingleRuleTac
  let ruleTacDecl :=
    mkDefinitionValEx `instantiatedSmtCoreRuleTac [] ruleTacType ruleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedSmtCoreRuleTac]
  addAndCompile $ Declaration.defnDecl ruleTacDecl
  let ruleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedSmtCoreRuleTac)))
  Aesop.evalAesop (← `(tactic| aesop? (add unsafe 1% tactic $ruleTacStx)))

example (a b : Int) : a + b = b + a := by foo -- Try this: smt

syntax (name := bar) "bar" ("[" term,* "]")? : tactic

def parseBar : Syntax → TacticM (List (Expr × Syntax))
  | `(tactic| bar) => pure []
  | `(tactic| bar [ $[$ns],* ]) => do
      let exprs ← ns.toList.mapM (fun t => elabTerm t.raw none)
      return List.zip exprs ns.toList
  | _ => throwError "[foo]: unexpected syntax"

#check default

@[tactic bar] def evalBar : Tactic := fun stx => withMainContext do
  let names ← parseBar stx
  let mvar ← getMainGoal
  let goal_copy := (← Meta.mkFreshExprMVar (← mvar.getType)).mvarId!
  let res ← Smt.smt default goal_copy (names.map (fun p => p.1)).toArray
  /- let r : Expr := names.head!.1 -/
  /- let res ← Smt.smt default goal_copy #[q($r)] -/
  let unsat_core ←
    match res with
    | .unsat _ uc => pure uc
    | _ => throwError "[Smt.smt]: Got SAT from solver"
  let names' := unsat_core.map (fun e => (names.lookup e).get!)
  let names' ← names'.mapM f'
  let idents ← names'.mapM (fun i => `(Smt.Tactic.smtHintElem| $i:term))
  let stx ← `(tactic| smt [$(idents),*])
  withoutRecover $ evalTactic stx

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  foo [h1]
