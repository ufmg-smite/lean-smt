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

-- The type and the corresponding syntax
abbrev Premises := List (Expr × Syntax)

def cast_stx {m : Type → Type} [Monad m] (stx : Syntax) : m (TSyntax `term) :=
  match stx with
  | `($t) => return t

def createArrow (es : List Expr) (e : Expr) : Expr :=
  match es with
  | [] => e
  | hd :: tl =>
    let r : Q(Prop) := createArrow tl e
    let hd : Q(Prop) := hd
    q($hd -> $r)

def smtSingleRuleTac (ps : Premises) (includeLCtx : Bool) : SingleRuleTac := fun input => do
  let preState ← saveState
  input.goal.withContext do
    let g ← input.goal.getType
    let types := ps.map (fun p => p.1)
    let arrow := createArrow types g
    let mv ← mkFreshExprMVar arrow
    let (hs, mv') ← mv.mvarId!.introN ps.length
    let res ← Smt.smt default mv' (hs.map (fun fv => .fvar fv))
    let unsat_core ←
      match res with
      | .unsat mvs uc => pure uc
      | _ => throwError "[Smt.smt]: Got SAT from solver"
    let names := unsat_core.map (fun e => let idx := hs.findIdx (fun z => .fvar z == e); ps[idx]!.2)
    let namesT ← names.mapM cast_stx
    let idents ← namesT.mapM (fun i => `(Smt.Tactic.smtHintElem| $i:term))
    let stx ←
      if includeLCtx && !unsat_core.isEmpty then
        `(tactic| smt [*, $(idents),*])
      else if includeLCtx && unsat_core.isEmpty then
        `(tactic| smt [*])
      else if !includeLCtx && !unsat_core.isEmpty then
        `(tactic| smt [$(idents),*])
      else -- if !includeLCtx && unsat_core.isEmpty
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

def parseFoo : Syntax → TacticM (List (Expr × Syntax))
  | `(tactic| foo) => pure []
  | `(tactic| foo [ $[$ns],* ]) => do
      let hints ← ns.mapM (fun n => cast_stx n)
      let hints ← hints.mapM (fun n => `(Smt.Tactic.smtHintElem| $n:term))
      let (_, elabedHints) ← Smt.Tactic.elabHints (← `(Smt.Tactic.smtHints| [$(hints),*]))
      let types ← elabedHints.mapM (fun h => Meta.inferType h)
      return List.zip types.toList ns.toList
  | _ => throwError "[foo]: unexpected syntax"

@[tactic foo]
def evalFoo : Tactic := fun stx => withMainContext do
  let typesAndStx : List (Expr × Syntax) ← parseFoo stx
  let ruleTacVal ← mkAppM `smtSingleRuleTac #[q($typesAndStx), q(false)]
  let ruleTacType := mkConst `Aesop.SingleRuleTac
  let ruleTacDecl :=
    mkDefinitionValEx `instantiatedSmtCoreRuleTac [] ruleTacType ruleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedSmtCoreRuleTac]
  addAndCompile $ Declaration.defnDecl ruleTacDecl
  let ruleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedSmtCoreRuleTac)))
  Aesop.evalAesop (← `(tactic| aesop? (add unsafe 1% tactic $ruleTacStx)))

example (a b : Int) : a + b = b + a := by foo -- Try this: smt

example (ε : Real) (h1 : ε > 0) (h2 : ε ≠ 10) : ε / 2 + ε / 3 + ε / 7 < ε := by
  foo [h1, h2]
    /- Try this: -/
    /-   simp_all only [gt_iff_lt, ne_eq] -/
    /-   smt [h1] -/
