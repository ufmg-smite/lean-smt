import Smt.Translate.Solver

open Smt Translate Solver

def query : SolverM Sexp := do
  setLogic "QF_UF"
  assert (.symbolT "false")
  _ ← checkSat
  getProof

def main : IO Unit := do
  let ss ← createFromKind .cvc5 "cvc5" none
  let (res, ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: unsat\n\nproof:\n{unquote (toString res)}"
where
  unquote s := s.extract ⟨8⟩ (s.endPos - ⟨2⟩)

#eval main
