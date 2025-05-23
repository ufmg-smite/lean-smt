import Smt.Translate.Solver

open Smt Translate Solver

def cvc5.os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"

def cvc5.arch :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else "arm64"

def cvc5.target := s!"{os}-{arch}-static"

def query : SolverM (Result × Sexp) := do
  setLogic "LIA"
  setOption "produce-models" "true"
  declareConst "x" (.symbolT "Int")
  return (← checkSat, ← getModel)

def main : IO Unit := do
  let ss ← createFromKind .cvc5 s!".lake/packages/cvc5/cvc5-{cvc5.target}/bin/cvc5" none
  let ((res, model), ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: {res}\n\nmodel:\n{model}"

#eval main
