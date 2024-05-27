import Smt.Translate.Solver

open Smt Translate Solver

def query : SolverM Sexp := do
  setLogic "QF_UF"
  assert (.symbolT "false")
  _ ← checkSat
  getProof

def main : IO Unit := do
  let ss ← createFromKind .cvc5 ".lake/packages/cvc5/.lake/cvc5/bin/cvc5" none
  let (res, ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: unsat\n\nproof:\n{res}"

#eval main
