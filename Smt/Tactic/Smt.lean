/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Dsl.Sexp
import Smt.Query
import Smt.Solver

namespace Smt

open Lean
open Lean.Elab
open Lean.Elab.Tactic

initialize
  registerTraceClass `smt.debug
  registerTraceClass `smt.debug.attr
  registerTraceClass `smt.debug.query
  registerTraceClass `smt.debug.translator

syntax smtHints := ("[" ident,* "]")?
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

def prepareSmtQuery (hints : TSyntax `smtHints) : TacticM Solver := do
  -- 1. Get the current main goal.
  let goalType ← Tactic.getMainTarget
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g => do
  -- 2. Get the hints passed to the tactic.
  let mut hs ← parseHints hints
  hs := hs.eraseDups
  -- 3. Generate the SMT query.
  let mut solver := Solver.mk []
  Query.generateQuery g hs solver

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let goalType ← Tactic.getMainTarget
  let solver ← prepareSmtQuery ⟨stx[1]⟩
  let query := solver.queryToString
  -- 4. Run the solver.
  let kind := smt.solver.kind.get (← getOptions)
  let path := smt.solver.path.get? (← getOptions) |>.getD kind.toDefaultPath
  -- Don't run solver if the server cancelled our task
  if (← IO.checkCanceled) then return
  let res ← if let `(smtTimeout| (timeout := $n)) := stx[2] then
    solver.checkSat kind path (some n.getNat)
  else
    solver.checkSat kind path
  -- 5. Print the result.
  logInfo m!"goal: {goalType}\n\nquery:\n{query}\nresult: {res}"
  let out ← match Sexp.parse res with
    | .ok out => pure out
    | .error e => throwError "cannot parse solver output: {e}"
  if out.contains sexp!{sat} then
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
    -- TODO ask for countermodel and print
  else if !out.contains sexp!{unsat} then
    throwError "unable to prove goal"

@[tactic smtShow] def evalSmtShow : Tactic := fun stx => withMainContext do
  let goalType ← Tactic.getMainTarget
  let solver ← prepareSmtQuery ⟨stx[1]⟩
  let query := solver.queryToString
  -- 4. Print the query.
  logInfo m!"goal: {goalType}\n\nquery:\n{query}"

end Smt
