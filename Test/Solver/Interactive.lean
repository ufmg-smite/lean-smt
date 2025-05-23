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

open Term in
def query : SolverM Result := do
  setLogic "LIA"
  declareConst "x" (symbolT "Int")
  declareConst "y" (symbolT "Int")
  assert (mkApp2 (symbolT "<") (symbolT "x") (symbolT "y"))
  let mut res ← checkSat
  if res = .sat then
    assert (mkApp2 (symbolT ">")
                    ((mkApp2 (symbolT "+") (symbolT "x") (literalT "1")))
                    (symbolT "y"))
    res ← checkSat
  return res

def main : IO Unit := do
  let ss ← createFromKind .cvc5 s!".lake/packages/cvc5/cvc5-{cvc5.target}/bin/cvc5" none
  let (res, ss) ← StateT.run query ss
  _ ← StateT.run exit ss
  println! "query:\n{Command.cmdsAsQuery ss.commands.reverse}\n\nres: {res}"

#eval main
