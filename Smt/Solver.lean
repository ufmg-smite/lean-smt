import Lean
import Smt.Term

namespace Smt

inductive Kind where
  | cvc5
  | z3
  deriving Inhabited

/-- The data-structure for SMT-LIB based solver. -/
structure Solver where
  commands : List String
  deriving Inhabited

namespace Solver

variable (solver : Solver)

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : Solver :=
  ⟨s!"(set-logic {l})" :: solver.commands⟩

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : Solver :=
  ⟨s!"(declare-sort {id} {Nat.toDigits 10 n})" :: solver.commands⟩

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : Solver :=
  ⟨(s!"(define-sort {id} ({paramsToString ss}) {s})") :: solver.commands⟩
  where
    paramsToString (ss) := String.intercalate " " (ss.map Term.toString)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : Solver :=
  ⟨s!"(declare-const {id} {s})" :: solver.commands⟩

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : Solver :=
  ⟨s!"(declare-fun {id} {s})" :: solver.commands⟩

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  Solver :=
  ⟨s!"(define-fun {id} ({paramsToString ps}) {s} {t})" :: solver.commands⟩
  where
    paramsToString (ps : List (String × Term)) : String :=
      String.intercalate " " (ps.map (fun (n, s) => s!"({n} {s})"))

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : Solver :=
  ⟨s!"(assert {t})" :: solver.commands⟩

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat (kind : Kind) (path : String) : IO String := do
  let proc ← IO.Process.spawn {
    stdin := IO.Process.Stdio.piped
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd := path
    args := match kind with
      | Kind.cvc5 => #["-q"]
      | Kind.z3   => #["-in"]
  }
  let query := String.intercalate
                 "\n" ("(exit)\n" :: "(check-sat)" :: solver.commands).reverse
  proc.stdin.putStr query
  proc.stdin.flush
  _ ← proc.wait
  proc.stdout.readToEnd

end Solver
end Smt
