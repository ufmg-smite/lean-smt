import Lean
import Smt.Solver
import Smt.Util
import Smt.Term

namespace Smt

open Lean.Elab
open Lean.Elab.Tactic
open Smt.Solver
open Smt.Util

syntax "check_sat" : tactic

/-- `check_sat` Converts the current goal into an SMT query and checks if it is satisfiable. -/
@[tactic tacticCheck_sat] def evalCheckSat : Tactic := fun stx => do
  let goal ← Tactic.getMainTarget
  -- Create a mapping from the free vars in the goal to their infos
  -- (i.e., user-friendly names and types).
  let mut fvars := getFVars goal
  fvars := List.eraseDups fvars
  let temp := List.mapM Lean.Meta.getFVarLocalDecl fvars
  let localDecls ← temp
  let ctx : Util.Context := {
    bvars := []
    fvars := List.foldr (fun (v, d) m => m.insert v d) Std.mkHashMap (List.zip fvars localDecls)
  }
  -- Declare those free vars as constants uninterpreted functions.
  let mut solver := Solver.mk []
  for (v, d) in List.zip fvars localDecls do
    solver := solver.declareConst (ctx.fvars.find! v).userName.toString (← exprToTerm' ctx d.type)
  -- Assert the goal.
  solver := solver.assert (← exprToTerm' ctx (Lean.mkNot goal))
  let query := String.intercalate "\n" ("(check-sat)\n" :: solver.commands).reverse
  -- Run the solver.
  let res ← solver.checkSat
  logInfo m!"goal: {goal}\n\nquery:\n{query}\nresult: {res}\nexpr ast: {exprToString goal}"

end Smt
