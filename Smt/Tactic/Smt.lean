/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Dsl.Sexp
import Smt.Reconstruct
import Smt.Reconstruct.Prop.Lemmas
import Smt.Translate.Query
import Smt.Util

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

initialize
  registerTraceClass `smt.debug
  registerTraceClass `smt.debug.attr
  registerTraceClass `smt.debug.translate.query
  registerTraceClass `smt.debug.translate.expr

syntax smtHints := ("[" term,* "]")?
syntax smtTimeout := ("(timeout := " num ")")?

/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the current goal. However, that is not always enough:
```lean
def modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` and `hpq` required to prove the theorem. To
pass hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
def modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
```
The tactic then generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(declare-const p Bool)
(assert p)
(assert (=> p q))
(check-sat)
```
-/
syntax (name := smt) "smt" smtHints smtTimeout : tactic

/-- Like `smt`, but just shows the query without invoking a solver. -/
syntax (name := smtShow) "smt_show" smtHints : tactic

def parseHints : TSyntax `smtHints → TacticM (List Expr)
  | `(smtHints| [ $[$hs],* ]) => hs.toList.mapM (fun h => elabTerm h.raw none)
  | `(smtHints| ) => return []
  | _ => throwUnsupportedSyntax

def parseTimeout : TSyntax `smtTimeout → TacticM (Option Nat)
  | `(smtTimeout| (timeout := $n)) => return some n.getNat
  | `(smtTimeout| ) => return some 5
  | _ => throwUnsupportedSyntax

def withProcessedHints (hs : List Expr) (k : List Expr → TacticM α): TacticM α :=
  withProcessHints' hs [] k
where
  withProcessHints' (hs : List Expr) (fvs : List Expr) (k : List Expr → TacticM α): TacticM α := do
    match hs with
    | [] => k fvs
    | h :: hs =>
      if h.isFVar || h.isConst then
        withProcessHints' hs (h :: fvs) k
      else
        let mv ← Tactic.getMainGoal
        let mv ← mv.assert (← mkFreshId) (← Meta.inferType h) h
        let ⟨fv, mv⟩ ← mv.intro1
        Tactic.replaceMainGoal [mv]
        withMainContext (withProcessHints' hs (.fvar fv :: fvs) k)

def prepareSmtQuery (hs : List Expr) : TacticM (List Command) := do
  let goalType ← Tactic.getMainTarget
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs

def elabProof (text : String) : TacticM Name := do
  let name ← mkFreshId
  let name := Name.str name.getPrefix ("th0" ++ name.toString)
  let text := text.replace "th0" s!"{name}"
  let (env, log) ← process text (← getEnv) .empty "<proof>"
  _ ← modifyEnv (fun _ => env)
  for m in log.msgs do
    trace[smt.debug.reconstruct] (← m.toString)
  if log.hasErrors then
    throwError "encountered errors elaborating cvc5 proof"
  return name

def evalAnyGoals (tactic : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tactic
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  setGoals mvarIdsNew.toList

private def addDeclToUnfoldOrTheorem (thms : Meta.SimpTheorems) (e : Expr) : MetaM Meta.SimpTheorems := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← Meta.isProp info.type) then
      thms.addConst declName
    else
      thms.addDeclToUnfold declName
  else
    thms.add (.fvar e.fvarId!) #[] e

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let mv ← Util.rewriteIffMeta (← Tactic.getMainGoal)
  Tactic.replaceMainGoal [mv]
  let goalType : Q(Prop) ← mv.getType
  -- 1. Get the hints passed to the tactic.
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  withProcessedHints hs fun hs => do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs
  let cmds := .setLogic "ALL" :: cmds
  trace[smt.debug] m!"goal: {goalType}"
  trace[smt.debug] m!"\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  let timeout ← parseTimeout ⟨stx[2]⟩
  -- 3. Run the solver.
  let res ← prove (Command.cmdsAsQuery cmds) timeout
  -- 4. Print the result.
  -- logInfo m!"\nresult: {res.toString}"
  match res with
  | .error e =>
    -- 4a. Print error reason.
    trace[smt.debug] m!"\nerror reason:\n{repr e}\n"
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
  | .ok pf =>
    let (p, mvs) ← reconstructProof pf
    let ts ← hs.mapM (fun h => Meta.inferType h)
    let mut gs ← (← Tactic.getMainGoal).apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ts q(Prop), goalType])
    Tactic.replaceMainGoal (gs ++ mvs)
    let hs := p :: hs
    for h in hs do
      evalAnyGoals do
        let gs ← (← Tactic.getMainGoal).apply h
        Tactic.replaceMainGoal gs

@[tactic smtShow] def evalSmtShow : Tactic := fun stx => withMainContext do
  let mv ← Util.rewriteIffMeta (← Tactic.getMainGoal)
  let goalType ← mv.getType
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  withProcessedHints hs fun hs => do
  let cmds ← prepareSmtQuery hs
  let cmds := cmds ++ [.checkSat]
  logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery cmds}"

end Smt
