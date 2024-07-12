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
import Smt.Preprocess
import Smt.Util

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

def prepareSmtQuery (hs : List Expr) (goalType : Expr) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs

def withProcessedHints (mv : MVarId) (hs : List Expr) (k : MVarId → List Expr → MetaM α): MetaM α :=
  go mv hs [] k
where
  go (mv : MVarId) (hs : List Expr) (fvs : List Expr) (k : MVarId → List Expr → MetaM α): MetaM α := do
    match hs with
    | [] => k mv fvs
    | h :: hs =>
      if h.isFVar || h.isConst then
        go mv hs (h :: fvs) k
      else
        let mv ← mv.assert (← mkFreshId) (← Meta.inferType h) h
        let ⟨fv, mv⟩ ← mv.intro1
        go mv hs (.fvar fv :: fvs) k

def smt (mv : MVarId) (hs : List Expr) (timeout : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType : Q(Prop) ← mv.getType
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs (← mv.getType)
  let cmds := .setLogic "ALL" :: cmds
  trace[smt] "goal: {goalType}"
  trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- 3. Run the solver.
  let res ← solve (Command.cmdsAsQuery cmds) timeout
  -- 4. Print the result.
  -- trace[smt] "\nresult: {res}"
  match res with
  | .error e =>
    -- 4a. Print error reason.
    trace[smt] "\nerror reason:\n{repr e}\n"
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
  | .ok pf =>
    -- 4b. Reconstruct proof.
    let (p, hp, mvs) ← reconstructProof pf
    let mv ← mv.assert (← mkFreshId) p hp
    let ⟨_, mv⟩ ← mv.intro1
    let ts ← hs.mapM Meta.inferType
    let mut gs ← mv.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ts q(Prop), goalType])
    mv.withContext (gs.forM (·.assumption))
    return mvs

namespace Tactic

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

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let mvs ← Smt.smt (← Tactic.getMainGoal) (← parseHints ⟨stx[1]⟩) (← parseTimeout ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs

@[tactic smtShow] def evalSmtShow : Tactic := fun stx => withMainContext do
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let hs ← parseHints ⟨stx[1]⟩
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType ← mv.getType
  let cmds ← prepareSmtQuery hs (← mv.getType)
  let cmds := cmds ++ [.checkSat]
  logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery cmds}"

end Smt.Tactic
