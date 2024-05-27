/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Batteries.Data.HashMap
import Smt.Commands
import Smt.Data.Sexp
import Smt.Term

open Batteries

namespace Smt

inductive Kind where
  --| boolector
  | cvc5
  | vampire
  --| yices
  | z3
deriving DecidableEq, Inhabited, Hashable

def allKinds : List Kind := [
  -- Kind.boolector,
  Kind.cvc5,
  Kind.vampire,
  -- Kind.yices,
  Kind.z3
]

instance : ToString Kind where
  toString
    --| .boolector => "boolector"
    | .cvc5      => "cvc5"
    | .vampire   => "vampire"
    --| .yices     => "yices"
    | .z3        => "z3"

instance : Lean.KVMap.Value Kind where
  toDataValue k := toString k
  ofDataValue?
    --| "boolector" => Kind.boolector
    | "cvc5"      => Kind.cvc5
    | "vampire"   => Kind.vampire
    --| "yices"     => Kind.yices
    | "z3"        => Kind.z3
    | _           => none

/-- What the binary for a given solver is usually called. -/
def Kind.toDefaultPath : Kind → String
  --| .yices => "yices-smt2"
  | k      => toString k

/-- Result of an SMT query. -/
inductive Result where
  | sat     : Result
  | unsat   : Result
  | unknown : Result
  | timeout : Result
deriving DecidableEq, Inhabited

instance : ToString Result where
  toString : Result → String
    | .sat     => "sat"
    | .unsat   => "unsat"
    | .unknown => "unknown"
    | .timeout => "timeout"

/-- The data-structure for the state of the generic SMT-LIB solver. -/
structure SolverState where
  commands : List Command
  args : HashMap Kind (Array String)

abbrev SolverT (m) [Monad m] [MonadLiftT IO m] := StateT SolverState m

abbrev SolverM := SolverT IO

namespace Solver

variable [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]

def addCommand (c : Command) : SolverT m Unit := do
  let state ← get
  set { state with commands := c :: state.commands }

def addCommands : List Command → SolverT m Unit := (List.forM · addCommand)

/-- Create an instance of a pre-configured SMT solver. -/
def create (timeoutSecs : Nat) : IO SolverState := do
  let args : HashMap Kind (Array String) := HashMap.ofList [
    --(.boolector, #["--smt2", "--time", toString timeoutSecs]),
    (.cvc5,      #["--quiet", "--incremental", "--lang", "smt", "--dag-thresh=0", "--enum-inst", "--tlimit", toString (1000 * timeoutSecs)]),
    (.vampire,   #["--input_syntax", "smtlib2", "--output_mode", "smtcomp", "--time_limit", toString timeoutSecs]),
    --(.yices,     #["--timeout", toString timeoutSecs]),
    (.z3,        #["-smt2", s!"-T:{timeoutSecs}"])
  ]
  return ⟨[], args⟩

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : SolverT m Unit := addCommand (.setLogic l)

/-- Set option `k` to value `v`. -/
def setOption (k : String) (v : String) : SolverT m Unit := addCommand (.setOption k v)

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : SolverT m Unit := addCommand (.declareSort id n)

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : SolverT m Unit :=
  addCommand (.defineSort id ss s)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : SolverT m Unit := addCommand (.declare id s)

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : SolverT m Unit := addCommand (.declare id s)

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := addCommand (.defineFun id ps s t false)

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := addCommand (.defineFun id ps s t true)

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : SolverT m Unit := addCommand (.assert t)

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat : SolverT m Result := do
  addCommand .checkSat
  let state ← get

  let mut args : Array String := #[]

  for kind in allKinds do
    args := args.push s!"--{kind.toDefaultPath}"
    args := args.push $ state.args[kind].get!.foldl (fun r s => r ++ " " ++ s) ""

  let proc ← IO.Process.spawn {
    cmd := "smt-portfolio"
    args := args
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

  for c in state.commands.reverse ++ [.exit] do
    proc.stdin.putStr s!"{c}\n"

  proc.stdin.flush
  let (_, proc) ← proc.takeStdin
  let _ ← proc.wait

  match (← proc.stdout.readToEnd).trim with
  | "sat"     => return .sat
  | "unsat"   => return .unsat
  | "unknown" => return .unknown
  | "timeout" => return .timeout
  | out => (throw (IO.userError s!"unexpected solver output\nstdout: {out}\nstderr:{← proc.stderr.readToEnd}") : IO _)

end Smt.Solver
