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

def query : SolverM Sexp := do
  setLogic "QF_UF"
  assert (.symbolT "false")
  _ ← checkSat
  getProof

def main : IO Unit := do
  let ss ← createFromKind .cvc5 s!".lake/packages/cvc5/.lake/cvc5-{cvc5.target}/bin/cvc5" none
  let (res, ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: unsat\n\nproof:\n{res}"

#eval main
