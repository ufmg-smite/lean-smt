import Lean
import Smt.Solver
import Smt.Util
import Smt.Term

namespace Smt

open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Smt.Solver
open Smt.Util

initialize
  Lean.registerTraceClass `Smt.debug

def queryToString (commands : List String) : String :=
  String.intercalate "\n" ("(check-sat)\n" :: commands).reverse

/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the goal. However, that is not always enough:
```lean
def modus_ponens (p q : Prop) (hp : p) (f : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` `f` required to prove the theorem. To pass
hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
def modus_ponens (p q : Prop) (hp : p) (f : p → q) : q := by
  smt [hp, f]
```
The tactic then generates the query below:
```smt2
(declare-const p Bool)
(declare-const q Bool)
(assert p)
(assert (=> p q))
(assert (not q))
(check-sat)
```
-/
syntax (name := smt) "smt" ("[" ident,+,? "]")? : tactic

def parseTactic : Lean.Syntax → TacticM (List Lean.Expr)
  | `(tactic| smt)       => []
  | `(tactic| smt [$[$hs],*]) => hs.toList.mapM (fun h => elabTerm h none)
  | _                    => throwUnsupportedSyntax

@[tactic smt] def evalSmt : Tactic := fun stx => do
  -- 1. Get the current main goal.
  let goal ← Tactic.getMainTarget
  -- 2. Get the free vars in the goal and the ones passed to the tactic.
  let mut hs := getFVars goal
  hs := hs ++ (← parseTactic stx)
  hs := hs.eraseDups
  hs ← fixedPoint getAllTypeFVars hs
  -- 3. If those free variables are hypothesis, assert them. Otherwise, declare those free vars
  --    as symbolic constants/uninterpreted functions.
  let mut solver := Solver.mk []
  for h in hs do
    let n ← match h with
      | Lean.Expr.fvar id .. => (← Lean.Meta.getLocalDecl id).userName.toString
      | Lean.Expr.const n .. => n.toString
      | _                    => throwUnsupportedSyntax
    -- logInfo m!"{v.fvarId!.name} {n}"
    let t ← Lean.Meta.inferType h
    let s ← exprToTerm t
    solver := if (← Lean.Meta.inferType t).isProp then solver.assert s else match s with
      | Term.Symbol .. => solver.declareConst n s
      | _             => solver.declareFun n s
  -- Assert the goal.
  solver := solver.assert (← exprToTerm (Lean.mkNot goal))
  let query := queryToString solver.commands
  -- Run the solver and print the result.
  let res ← solver.checkSat
  logInfo m!"goal: {goal}\n\nquery:\n{query}\nresult: {res}"

end Smt
