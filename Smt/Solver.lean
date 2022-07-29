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
  | cvc4
  | cvc5
  | z3
  | yices
  | boolector
  | vampire
  deriving Inhabited, DecidableEq

instance : ToString Kind where
  toString
    | .cvc4      => "cvc4"
    | .cvc5      => "cvc5"
    | .z3        => "z3"
    | .yices     => "yices"
    | .boolector => "boolector"
    | .vampire   => "vampire"

instance : Lean.KVMap.Value Kind where
  toDataValue k := toString k
  ofDataValue?
    | "cvc4"      => Kind.cvc4
    | "cvc5"      => Kind.cvc5
    | "z3"        => Kind.z3
    | "yices"     => Kind.yices
    | "boolector" => Kind.boolector
    | "vampire"   => Kind.vampire
    | _           => none

/-- What the binary for a given solver is usually called. -/
def Kind.toDefaultPath : Kind → String
  | .yices => "yices-smt2"
  | k      => toString k

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
open Term

variable (solver : Solver)

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : Solver :=
  ⟨s!"(set-logic {l})" :: solver.commands⟩

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : Solver :=
  ⟨s!"(declare-sort {quoteSymbol id} {n})" :: solver.commands⟩

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : Solver :=
  ⟨(s!"(define-sort {quoteSymbol id} ({paramsToString ss}) {s})") :: solver.commands⟩
  where
    paramsToString (ss) := String.intercalate " " (ss.map Term.toString)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : Solver :=
  ⟨s!"(declare-const {quoteSymbol id} {s})" :: solver.commands⟩

/-- Define a constant with name `id` sort `s`, and value `v`. -/
def defineConst (id : String) (s : Term) (v : Term) : Solver :=
  ⟨s!"(define-const {quoteSymbol id} {s} {v})" :: solver.commands⟩

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : Solver :=
  ⟨s!"(declare-fun {quoteSymbol id} {s})" :: solver.commands⟩

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  Solver :=
  ⟨s!"(define-fun {quoteSymbol id} ({paramsToString ps}) {s} {t})" :: solver.commands⟩
  where
    paramsToString (ps : List (String × Term)) : String :=
      String.intercalate " " (ps.map (fun (n, s) => s!"({quoteSymbol n} {s})"))

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term)
  (t : Term) :
  Solver :=
  ⟨s!"(define-fun-rec {quoteSymbol id} ({paramsToString ps}) {s} {t})" :: solver.commands⟩
  where
    paramsToString (ps : List (String × Term)) : String :=
      String.intercalate " " (ps.map (fun (n, s) => s!"({quoteSymbol n} {s})"))

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : Solver :=
  ⟨s!"(assert {t})" :: solver.commands⟩

def queryToString : String :=
  String.intercalate "\n" ("(check-sat)\n" :: solver.commands).reverse

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat (kind : Kind) (path : String) (timeoutSecs? : Option Nat := some 5) : IO String := do
  let mut args := match kind with
    | .cvc4      => #["--quiet", "--lang", "smt"]
    | .cvc5      => #["--quiet", "--lang", "smt"]
    | .z3        => #["-in", "-smt2"]
    | .yices     => #[]
    | .boolector => #["--smt2"]
    | .vampire   => #["--input_syntax", "smtlib2", "--output_mode", "smtcomp"]
  if let some secs := timeoutSecs? then
    args := args ++ match kind with
    | .cvc4      => #["--tlimit", toString (secs*1000)]
    | .cvc5      => #["--tlimit", toString (secs*1000)]
    | .z3        => #[s!"-T:{secs}"]
    | .yices     => #["--timeout", toString secs]
    | .boolector => #["--time", toString secs]
    | .vampire   => #["--time_limit", toString secs]
  let proc ← IO.Process.spawn {
    stdin := IO.Process.Stdio.piped
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd := path
    args
  }
  let query := solver.queryToString ++ "\n(exit)"
  proc.stdin.putStr query
  -- Close stdin to signal EOF to the solver.
  let (_, proc) ← proc.takeStdin
  _ ← proc.wait
  let out ← proc.stdout.readToEnd
  let err ← proc.stderr.readToEnd
  return s!"{out}{if err.isEmpty then "" else "\n"}{err}"

end Solver
end Smt
