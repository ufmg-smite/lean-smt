import Smt.Translate.Solver

open Smt Translate Solver

def query : SolverM Result := do
  setLogic "LIA"
  declareConst "x" (.symbolT "Int")
  declareConst "x" (.symbolT "Int")
  checkSat

def main : IO Unit := do
  let ss ← createFromKind .cvc5 ".lake/packages/cvc5/.lake/cvc5/bin/cvc5" none
  _ ← StateT.run query ss

#eval main
