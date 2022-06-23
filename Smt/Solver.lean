/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Term

namespace Smt

inductive Kind where
  | cvc5
  | z3
  | vampire
  deriving Inhabited

instance : ToString Kind where
  toString := fun
    | .cvc5 => "cvc5"
    | .z3 => "z3"
    | .vampire => "vampire"

instance : Lean.KVMap.Value Kind where
  toDataValue k := toString k
  ofDataValue?
    | "cvc5"    => Kind.cvc5
    | "z3"      => Kind.z3
    | "vampire" => Kind.vampire
    | _         => none

register_option smt.solver.kind : Kind := {
  defValue := Kind.cvc5
  descr := "The solver to use for solving the SMT query."
}

register_option smt.solver.path : String := {
  defValue := "cvc5"
  descr := "The path to the solver used for solving the SMT query."
}

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

/-- Define a constant with name `id` sort `s`, and value `v`. -/
def defineConst (id : String) (s : Term) (v : Term) : Solver :=
  ⟨s!"(define-const {id} {s} {v})" :: solver.commands⟩

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

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term)
  (t : Term) :
  Solver :=
  ⟨s!"(define-fun-rec {id} ({paramsToString ps}) {s} {t})" :: solver.commands⟩
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
      | Kind.cvc5    => #["-q"]
      | Kind.z3      => #["-in"]
      | Kind.vampire => #["--input_syntax", "smtlib2", "--output_mode", "smtcomp"]
  }
  let query := String.intercalate
                 "\n" ("(exit)\n" :: "(check-sat)" :: solver.commands).reverse
  proc.stdin.putStr query
  -- Close stdin to signal EOF to the solver.
  let (_, proc) ← proc.takeStdin
  _ ← proc.wait
  proc.stdout.readToEnd

end Solver
end Smt
