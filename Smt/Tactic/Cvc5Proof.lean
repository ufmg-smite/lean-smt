import Lean
import Smt.Reconstruction.Certifying.Util


open Lean Meta Elab Tactic Parser

open Smt.Reconstruction.Certifying

def lastStepName : Name := `lastStepCvc5

structure Tac where
  tacCode : String

inductive Step where
  | tac (name : Name) (goalStr : String) (tacCode : Tac) : Step
  | thm (name : Name) (goalStr : String) (thmName : Name) (args : List String) : Step
  -- the name in scope must match the list name in the list of steps
  | scope (name : Name) (goalStr : String) (steps : List Step) : Step

structure Cvc5Proof where
  steps: List Step
  -- again, must match the name and type of the last step
  goalStr: String
  name: Name

def strToStx (cat: Name) (str : String) : MetaM Syntax := do
  match runParserCategory (← getEnv) cat str with
  | .error e => throwError e
  | .ok stx  => pure stx

mutual

-- Register in the context the proof corresponding to this step.
partial def runStep (mvar: MVarId) : Step → TacticM MVarId
| .tac name goalStr tacStr => do
  let typeStx ← strToStx `term goalStr
  let tacStx ← strToStx `tactic tacStr.tacCode
  let haveStx ← `(tactic| have $(mkIdent name) : $(⟨typeStx⟩) := by $(⟨tacStx⟩))
  let mvars ← evalTacticAt haveStx mvar
  pure mvars.head!
| .thm name goalStr thmName args => do
  let typeStx ← strToStx `term goalStr
  let type ← elabTerm typeStx none
  let argsExpr: List Expr ←
    args.mapM (strToStx `term · >>= (elabTerm · none))
  let pf ← mkAppM thmName argsExpr.toArray
  let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type pf
  pure mvar'
| .scope name goalStr steps => do
  let cvc5Pf := { steps, name, goalStr }
  runProof mvar cvc5Pf

partial def runProof (mvar: MVarId) (pf : Cvc5Proof): TacticM MVarId := do
  pf.steps.foldlM (fun acc step => (runStep acc step)) mvar

end

-- Testing

def cvc5Proof1 : Cvc5Proof := {
  steps := [Step.tac `blah "True" ⟨"exact True.intro"⟩]
  name := `blah
  goalStr := "True"
}

def cvc5Proof2 : Cvc5Proof := {
  steps := [Step.thm `blah "True" `True.intro []]
  name := `blah
  goalStr := "True"
}

syntax (name := test) "test" term : tactic

@[tactic test] def evalTest : Tactic := fun stx =>
  withMainContext do
    let goal ← getMainGoal
    let id ← stxToNat ⟨stx[1]⟩
    let pf ←
      match id with
      | 1 => pure cvc5Proof1
      | 2 => pure cvc5Proof2
      | _ => throwError "unreachable"
    let mvar' ← runProof goal cvc5Proof1
    replaceMainGoal [mvar']
    withMainContext do
      let lctx ← getLCtx
      let some ldecl :=
        lctx.findFromUserName? cvc5Proof1.name | throwError "final step not defined"
      closeMainGoal ldecl.value

example : True := by test 1

example : True := by test 2
