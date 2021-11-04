import Smt.Term

namespace Smt

/-- The SMT Solver data-structure. -/
structure Solver where
  commands : List String

namespace Solver

/-- Set the SMT query logic to `l` -/
def setLogic (solver : Solver) (l : String) : Solver :=
  ⟨("(set-logic " ++ l ++ ")") :: solver.commands⟩

/-- Declare a symbolic constant with name `id` and sort `s` -/
def declareConst (solver : Solver) (id : String) (s : Term) : Solver :=
  ⟨("(declare-const " ++ id ++ " " ++ s.toString ++ ")") :: solver.commands⟩

/-- Declare an uninterpreted function with name `id` and sort `s` -/
def declareFun (solver : Solver) (id : String) (s : Term) : Solver :=
  ⟨("(declare-fun " ++ id ++ " " ++ s.toString ++ ")") :: solver.commands⟩

/-- Define a function with name `id`, parameters `ps`, co-domin `s`,
    and body `t` -/
def defineFun (solver : Solver) (id : String) (ps : List (String × Term)) (s : Term) (t : Term) : Solver :=
  ⟨("(define-fun " ++ id ++ " (" ++ paramsToString ps ++ ") " ++ s.toString ++ " "
    ++ t.toString ++ ")") :: solver.commands⟩
  where
    paramsToString (ps : List (String × Term)) : String :=
      String.intercalate " " (ps.map (fun (n, s) => "(" ++ n ++ " " ++ s.toString ++ ")"))

/-- Assert that proposition `t` is true. -/
def assert (solver : Solver) (t : Term): Solver := ⟨("(assert " ++ t.toString ++ ")") :: solver.commands⟩

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat (solver : Solver) : IO String := do
  let proc ← IO.Process.spawn {
    stdin := IO.Process.Stdio.piped
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd := "z3" -- "cvc5"
    args := #["-in"] -- #["-q", "--incremental"]
  }
  let query := String.intercalate "\n" ("(exit)\n" :: "(check-sat)" :: solver.commands).reverse
  proc.stdin.putStr query
  proc.stdin.flush
  _ ← proc.wait
  proc.stdout.readToEnd

end Solver
end Smt
