/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Commands
import Smt.Data.Sexp
import Smt.Term

namespace Smt

inductive Kind where
  | boolector
  | cvc4
  | cvc5
  | vampire
  | yices
  | z3
deriving DecidableEq, Inhabited

instance : ToString Kind where
  toString
    | .boolector => "boolector"
    | .cvc4      => "cvc4"
    | .cvc5      => "cvc5"
    | .vampire   => "vampire"
    | .yices     => "yices"
    | .z3        => "z3"

instance : Lean.KVMap.Value Kind where
  toDataValue k := toString k
  ofDataValue?
    | "boolector" => Kind.boolector
    | "cvc4"      => Kind.cvc4
    | "cvc5"      => Kind.cvc5
    | "vampire"   => Kind.vampire
    | "yices"     => Kind.yices
    | "z3"        => Kind.z3
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

/-- Result of an SMT query. -/
inductive Result where
  | sat     : Result
  | unsat   : Result
  | unknown : Result
deriving DecidableEq

instance : ToString Result where
  toString : Result → String
    | .sat     => "sat"
    | .unsat   => "unsat"
    | .unknown => "unknown"

/-- The data-structure for the state of the generic SMT-LIB solver. -/
structure SolverState where
  commands : List Command
  proc : IO.Process.Child ⟨.piped, .piped, .piped⟩

abbrev SolverT (m) [Monad m] [MonadLiftT IO m] := StateT SolverState m

abbrev SolverM := SolverT IO

namespace Solver

variable [Monad m] [MonadLiftT IO m]

def emitCommand (c : Command) : SolverT m Unit := do
  let state ← get
  set { state with commands := c :: state.commands }
  state.proc.stdin.putStr s!"{c}\n"
  state.proc.stdin.flush

def emitCommands : List Command → SolverT m Unit := (List.forM · emitCommand)

private def getSexp : SolverT m Sexp := do
  let state ← get
  let mut out ← state.proc.stdout.getLine
  let mut parseRes := Sexp.parseOne out
  while !(← (state.proc.stdout.isEof : IO _)) && parseRes matches .error (.incomplete _) do
    out := out ++ (← state.proc.stdout.getLine)
    parseRes := Sexp.parseOne out
  match parseRes with
  | .ok sexp!{(error {.atom e})} => (throw (IO.userError (unquote e)) : IO _)
  | .ok sexp => return sexp
  | .error e =>
    let err ← state.proc.stderr.readToEnd
    (throw (IO.userError (parseErrMsg e out err)) : IO _)
where
  unquote s := s.extract ⟨1⟩ ⟨s.length - 1⟩
  parseErrMsg (e : Sexp.ParseError) (out err : String) :=
    s!"could not parse solver output: {e}\nsolver stdout:\n{out}\nsolver stderr:\n{err}"

/-- Create an instance of a generic SMT solver.
    Note: `args` is only for enabling interactive SMT-LIB interface for solvers. To set other
          options, use `setOption` command. -/
def create (path : String) (args : Array String) : IO SolverState := do
  let proc ← IO.Process.spawn {
    stdin := .piped
    stdout := .piped
    stderr := .piped
    cmd := path
    args := args
  }
  return ⟨[], proc⟩

/-- Create an instance of a pre-configured SMT solver. -/
def createFromKind (kind : Kind) (path : Option String) (timeoutSecs : Option Nat) :
  IO SolverState := do
  let mut args := kindToArgs kind
  if let some secs := timeoutSecs then
    args := args ++ timeoutArgs secs kind
  create (path.getD kind.toDefaultPath) args
where
  kindToArgs : Kind → Array String
    | .boolector => #["--smt2"]
    | .cvc4      => #["--quiet", "--incremental", "--lang", "smt"]
    | .cvc5      => #["--quiet", "--incremental", "--lang", "smt"]
    | .vampire   => #["--input_syntax", "smtlib2", "--output_mode", "smtcomp"]
    | .yices     => #[]
    | .z3        => #["-in", "-smt2"]
  timeoutArgs (secs : Nat): Kind → Array String
    | .boolector => #["--time", toString secs]
    | .cvc4      => #["--tlimit", toString (1000*secs)]
    | .cvc5      => #["--tlimit", toString (1000*secs)]
    | .vampire   => #["--time_limit", toString secs]
    | .yices     => #["--timeout", toString secs]
    | .z3        => #[s!"-T:{secs}"]

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : SolverT m Unit := emitCommand (.setLogic l)

/-- Set option `k` to value `v`. -/
def setOption (k : String) (v : String) : SolverT m Unit := emitCommand (.setOption k v)

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : SolverT m Unit := emitCommand (.declareSort id n)

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : SolverT m Unit :=
  emitCommand (.defineSort id ss s)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : SolverT m Unit := emitCommand (.declare id s)

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : SolverT m Unit := emitCommand (.declare id s)

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := emitCommand (.defineFun id ps s t false)

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := emitCommand (.defineFun id ps s t true)

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : SolverT m Unit := emitCommand (.assert t)

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat : SolverT m Result := do
  emitCommand .checkSat
  let out ← getSexp
  let res ← match out with
    | "sat"     => return .sat
    | "unsat"   => return .unsat
    | "unknown" => return .unknown
    | _ => (throw (IO.userError s!"unexpected solver output: {repr out}") : IO _)
  return res

/- TODO: We should probably parse the returned string into `Command`s or `String × Term`s. This is
   bit tricky because we need to differentiate between literals and (user-defined) symbols. It
   should be possible, however, because we store a list of all executed commands. -/
/-- Return the model for a `sat` result. -/
def getModel : SolverT m String := do
  emitCommand .getModel
  prettyPrint <$> getSexp
where
  prettyPrint : Sexp → String
    | .atom _  => unreachable!
    | .expr es => match es with
      | [] => "()"
      | es => "(\n" ++ String.intercalate "\n" (es.map toString) ++ "\n)"

/-- Check if the query given so far is satisfiable and return the result. -/
def exit : SolverT m UInt32 := do
  emitCommand .exit
  let state ← get
  -- Close stdin to signal EOF to the solver.
  let (_, proc) ← state.proc.takeStdin
  proc.wait

end Smt.Solver
