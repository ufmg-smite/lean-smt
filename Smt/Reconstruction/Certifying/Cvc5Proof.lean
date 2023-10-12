import Smt
import Lean

open Lean Parser Elab Tactic Meta

-- Example: turning a String into a Tactic (typed Syntax for Tactic)
syntax (name := tmp) "tmp" : tactic

@[tactic tmp] def evalTmp : Tactic := fun _ =>
  withMainContext do
    let ictx: InputContext := {
      input := "trivial"
      fileName := default
      fileMap := default
    }
    let dummyEnv ← mkEmptyEnvironment
    let parserState := tacticParser.fn.run ictx { env := dummyEnv, options := {} } default (mkParserState ictx.input)
    let arrStx := SyntaxStack.extract parserState.stxStack 0 1
    let stx := arrStx.get! 0
    let stx: TSyntax `tactic := ⟨stx⟩ 
    evalTactic $ ← `(tactic| $stx)

structure Tac where
  stx : String -- syntax for the tactic, including all parameters

structure Thm where
  thmName : Name
  args    : List Name

structure Step (Pf : Type) where
  name : Name
  type : String -- avoid building Exprs on C++, lets build the string and run the parser
  pf   : Pf

mutual
  inductive Pf where
    | tac : Tac → Pf
    | thm : Thm → Pf
    | scope (name : Name) (type : Expr) : Cvc5Proof → Pf
  inductive Cvc5Proof where
    | steps : List (Step Pf) → Cvc5Proof
end

-- we will define a function that takes a step and introduces the Name
-- with the given type in the context, using pf
