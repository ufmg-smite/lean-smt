import Smt.Solver

open Smt Solver

def query : SolverM Result := do
  setLogic "LIA"
  declareConst "x" (.symbolT "Int")
  declareConst "x" (.symbolT "Int")
  checkSat

def main : IO Unit := do
  let ss ← createFromKind .cvc5 "cvc5" none
  _ ← StateT.run query ss

#eval main
