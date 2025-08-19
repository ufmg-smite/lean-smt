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
abbrev Premises := List (String × Expr)

-- TODO: For now we just produce `smt` with all facts included. Once we can extract and parse the unsat core we
-- will change this function to filter the relevant premises and produce a tactic invocation with just those,
-- like in lean-hammer.
def smtSingleRuleTac (ps : Premises) (includeLCtx : Bool) : SingleRuleTac := fun input => do
  let preState ← saveState
  input.goal.withContext do
    let idents := ps.map (fun p => Lean.mkIdent p.1.toName)
    let stx ←
      if includeLCtx && !ps.isEmpty then
        `(tactic| smt [*, $(idents.toArray),*])
      else if includeLCtx && ps.isEmpty then
        `(tactic| smt [*])
      else if !includeLCtx && !ps.isEmpty then
        `(tactic| smt [$(idents.toArray),*])
      else -- if !includeLCtx && ps.isEmpty
        `(tactic| smt)
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

def parseFoo : Syntax → TacticM (List (String × Expr))
  | `(tactic| foo) => pure []
  | `(tactic| foo [ $[$ns],* ]) => do
      let terms : List String := ns.toList.map (fun n => n.raw.getId.toString)
      let exprs ← ns.toList.mapM (fun t => elabTerm t.raw none)
      return List.zip terms exprs
  | _ => throwError "[foo]: unexpected syntax"

@[tactic foo]
def evalFoo : Tactic := fun stx => withMainContext do
  let names : List (String × Expr) ← parseFoo stx
  let ruleTacVal ← mkAppM `smtSingleRuleTac #[q($names), q(false)]
  let ruleTacType := mkConst `Aesop.SingleRuleTac
  let ruleTacDecl :=
    mkDefinitionValEx `instantiatedSmtCoreRuleTac [] ruleTacType ruleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedSmtCoreRuleTac]
  addAndCompile $ Declaration.defnDecl ruleTacDecl
  let ruleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedSmtCoreRuleTac)))
  evalTactic (← `(tactic| aesop? (add unsafe 1% tactic $ruleTacStx)))

example (a b : Int) : a + b = b + a := by foo -- Try this: smt

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  foo [h1] -- Try this: simp_all only [gt_iff_lt]; smt [h1]
