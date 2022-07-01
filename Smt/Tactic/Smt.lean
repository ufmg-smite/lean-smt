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
  registerTraceClass `smt.debug.transformer

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
syntax (name := smt) "smt" ("[" ident,* "]")? : tactic

def queryToString (commands : List String) : String :=
  String.intercalate "\n" ("(check-sat)\n" :: commands).reverse

def parseTactic : Syntax → TacticM (List Expr)
  | `(tactic| smt)              => pure []
  | `(tactic| smt [ $[$hs],* ]) => hs.toList.mapM (fun h => elabTerm h.raw none)
  | _                           => throwUnsupportedSyntax

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  -- 1. Get the current main goal.
  let goalType ← Tactic.getMainTarget
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g => do
  -- 2. Get the hints passed to the tactic.
  let mut hs ← parseTactic stx
  hs := hs.eraseDups
  -- 3. Generate the SMT query.
  let mut solver := Solver.mk []
  solver ← Query.generateQuery g hs solver
  let query := queryToString solver.commands
  -- 4. Run the solver.
  let kind := smt.solver.kind.get (← getOptions)
  let path := smt.solver.path.get? (← getOptions) |>.getD (toString kind)
  -- 5. Print the result.
  let res ← solver.checkSat kind path
  logInfo m!"goal: {goalType}\n\nquery:\n{query}\nresult: {res}"
  let out ← match Sexp.parse res with
    | .ok out => pure out
    | .error e => throwError "cannot parse solver output: {e}"
  if out.contains sexp!{sat} then
    throwError "unable to prove goal, it is false"
    -- TODO ask for countermodel and print
  else if !out.contains sexp!{unsat} then
    throwError "unable to prove goal"

end Smt
