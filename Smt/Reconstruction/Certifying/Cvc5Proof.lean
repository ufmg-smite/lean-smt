import Smt
import Lean

open Lean Parser Elab Tactic Meta

def foo : String := "trivial"

syntax (name := test) "test" : tactic

@[tactic test] def evalTest : Tactic := fun _ =>
  withMainContext do
    match runParserCategory (← getEnv) `tactic foo with
    | .error e => throwError e
    | .ok stx => evalTactic $ ← `(tactic| $(⟨stx⟩))

example : True := by
  test

structure Tac where
  stx : String

inductive Step where
  | tac (name : Name) (type : String) : Tac → Step
  | thm (name : Name) (type : String) (args : List Name) : Step
  | scope (name : Name) (type : String) (steps : List Step) : Step

-- we will define a function that takes a step and introduces the Name
-- with the given type in the context, using pf
abbrev Proof := List Step
