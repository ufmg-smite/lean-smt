import Smt.Term

namespace Smt

/-- The SMT Solver data-structure. -/
structure Solver where
  commands : List String

namespace Solver

/-- Declare a new constant with name `id` and type `t` -/
def declareConst (solver : Solver) (id : String) (t : Term) : Solver := ⟨("(declare-const " ++ id ++ " " ++ Term.toString t ++ ")") :: solver.commands⟩

/-- Assert that proposition `t` is true. -/
def assert (solver : Solver) (t : Term): Solver := ⟨("(assert " ++ t.toString ++ ")") :: solver.commands⟩

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat (solver : Solver) : IO String := do
  let proc ← IO.Process.spawn {
    stdin := IO.Process.Stdio.piped
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd := "z3"
    args := #["-in"]
  }
  let query := String.intercalate "\n" ("(exit)\n" :: "(check-sat)" :: solver.commands).reverse
  proc.stdin.putStr query
  proc.stdin.flush
  _ ← proc.wait
  proc.stdout.readToEnd

end Solver
end Smt
