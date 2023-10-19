import Lean
import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Boolean

open Lean Meta Elab Tactic Parser

open Smt.Reconstruction.Certifying

abbrev Tac := String

inductive Step where
  | intro (name : Name) : Step
  | tac (name : Name) (goalStr : String) (tacStr : Tac) : Step
  | thm (name : Name) (goalStr : String) (thmName : Name) (args : List String) : Step
  -- the name in scope must match the last name in the list of steps
  | scope (name : Name) (steps : List Step) : Step

structure Cvc5Proof where
  steps: List Step
  -- again, must match the name of the last step
  name: Name

def strToStx (cat: Name) (str : String) : MetaM Syntax := do
  match runParserCategory (← getEnv) cat str with
  | .error e => throwError e
  | .ok stx  => pure stx

mutual

-- Register in the context the proof corresponding to this step.
partial def runStep (mvar: MVarId) (step: Step) : TacticM MVarId :=
  mvar.withContext do
    match step with
    | .intro name => do
      let (_, mvar') ← mvar.intro name
      return mvar'
    | .tac name goalStr tacStr => do
      let typeStx ← strToStx `term goalStr
      let tacStx ← strToStx `tactic tacStr
      let haveStx ← `(tactic| have $(mkIdent name) : $(⟨typeStx⟩) := by $(⟨tacStx⟩))
      let mvars ← evalTacticAt haveStx mvar
      pure mvars.head!
    | .thm name goalStr thmName args => mvar.withContext do
      let typeStx ← strToStx `term goalStr
      let type ← elabTerm typeStx none
      let argsExpr: List Expr ←
        args.mapM (strToStx `term · >>= (elabTerm · none))
      let lctx ← getLCtx
      let pf ←
      match lctx.findFromUserName? thmName with
      | some ldecl => do
        pure (mkAppN ldecl.value argsExpr.toArray)
      | none =>
        mkAppM thmName argsExpr.toArray
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type pf
      pure mvar'
    | .scope name steps => do
      let cvc5Pf := { steps, name }
      runProof mvar cvc5Pf

partial def runProof (mvar: MVarId) (pf : Cvc5Proof): TacticM MVarId := do
  pf.steps.foldlM runStep mvar

end

-- Testing

def cvc5Proof1 : Cvc5Proof := {
  steps := [Step.tac `pf "True" "exact True.intro"]
  name := `pf
}

def cvc5Proof2 : Cvc5Proof := {
  steps := [Step.thm `pf "True" `True.intro []]
  name := `pf
}

def cvc5Proof3 : Cvc5Proof := {
  steps := [ .intro `lean_a0
           , .thm `pf "True" `lean_a0 []
           ]
  name := `pf
}

  /- theorem cvc5_th0 {P Q : Prop} : (Not (P → ((P → Q) → Q))) → False := -/
  /-   fun lean_a0 : (Not (P → ((P → Q) → Q))) => by -/
  /-     have lean_s0 : (Not ((P → Q) → Q)) := notImplies2 lean_a0 -/
  /-     have lean_s1 : (P → Q)             := notImplies1 lean_s0 -/
  /-     have lean_s2 : (Or (Not P) Q)      := impliesElim lean_s1 -/
  /-     have lean_s3 : P                   := notImplies1 lean_a0 -/
  /-     have lean_s4 : Q                   := -/
  /-       by R2 lean_s2, lean_s3, P, [1, 0] -/
  /-     have lean_s5 : (Not ((P → Q) → Q)) := notImplies2 lean_a0 -/
  /-     have lean_s6 : (Not Q)             := notImplies2 lean_s5 -/
  /-     exact (show False from contradiction lean_s4 lean_s6) -/

def cvc5Proof4: Cvc5Proof := {
  steps := [ .intro `lean_a0
           , .thm `pf "Not ((P -> Q) -> Q)" ``notImplies2 ["lean_a0"]
           ]
  name := `pf
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
      | 3 => pure cvc5Proof3
      | 4 => pure cvc5Proof4
      | _ => throwError "unreachable"
    let mvar' ← runProof goal pf
    replaceMainGoal [mvar']
    withMainContext do
      let lctx ← getLCtx
      let some ldecl :=
        lctx.findFromUserName? pf.name | throwError "final step not defined"
      closeMainGoal ldecl.value

example : True := by test 1

example : True := by test 2

example : False → False := by test 3

example : Not (P -> ((P -> Q) -> Q)) -> Not ((P -> Q) -> Q) := by test 4 -- ?
  /- intro h -/
  /- have h' := notImplies2 h -/

