import Smt.Translate.Solver

open Smt Translate Solver

def query : SolverM (Result × Sexp) := do
  setLogic "LIA"
  setOption "produce-models" "true"
  declareConst "x" (.symbolT "Int")
  return (← checkSat, ← getModel)

def main : IO Unit := do
  let ss ← createFromKind .cvc5 ".lake/packages/cvc5/.lake/cvc5/bin/cvc5" none
  let ((res, model), ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: {res}\n\nmodel:\n{model}"

#eval main
