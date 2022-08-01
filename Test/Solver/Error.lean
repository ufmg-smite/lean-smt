import Smt.Solver

open Smt Solver

def query : SolverM Result := do
  setLogic "LIA"
  declareConst "x" (.symbolT "Int")
  declareConst "x" (.symbolT "Int")
  checkSat

def main : IO Unit := do
  let ss ← createFromKind .cvc5 "cvc5"
  let (res, ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{ss.commands}\n\nres: {res}"

#eval main
