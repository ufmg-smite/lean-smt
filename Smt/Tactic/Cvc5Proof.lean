import Lean

import Smt.Reconstruction.Certifying.Resolution
import Smt.Reconstruction.Certifying.Util
import Smt.Reconstruction.Certifying.Boolean

open Lean
open Meta hiding contradiction
open Elab Tactic Parser

open Smt.Reconstruction.Certifying

abbrev Tac := String

inductive Step where
  -- intro $name
  | intro (name : Name) : Step
  -- have $name : $goal := by $tac
  | tac (name : Name) (goalStr : String) (tacStr : Tac) : Step
  -- have $name : $goal := $thmName $args
  | thm (name : Name) (goalStr : String) (thmName : Name) (args : List String) : Step
  -- have $name : ¬ $paramType ∨ $retType := scope (fun $scopedName => ...)
  -- NOTE: lastName must match the name introduced in the last step
  | scope (name : Name) (paramTypeStr retTypeStr : String) (scopedName lastName : Name) (steps : List Step) : Step

structure Cvc5Proof where
  steps: List Step
  -- must match the name introduced in the last step
  lastName: Name

def strToStx (cat: Name) (str: String) : MetaM Syntax := do
  match runParserCategory (← getEnv) cat str with
  | .error e => throwError e
  | .ok stx  => pure stx

def strToExpr (str: String) : TacticM Expr := do
  let stx ← strToStx `term str
  elabTerm stx none

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
      let [mvar'] ←
        evalTacticAt haveStx mvar | throwError "tactic generated many goals"
      pure mvar'
    | .thm name goalStr thmName args => do
      let type ← strToExpr goalStr
      let argsExpr: List Expr ←
        args.mapM strToExpr
      let lctx ← getLCtx
      let pf ←
      -- different treatment depending on whether thmName is a theorem
      -- or a hypothesis (lean_sx etc)
        match lctx.findFromUserName? thmName with
        | some ldecl => do
          pure (mkAppN (Expr.fvar ldecl.fvarId) argsExpr.toArray)
        | none => do
          mkAppM thmName argsExpr.toArray
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type pf
      return mvar'
    | .scope name paramTypeStr retTypeStr scopedName lastName steps => do
      let paramType ← strToExpr paramTypeStr
      let retType ← strToExpr retTypeStr
      let goalExpr :=
        mkApp2 (mkConst ``Or) (mkApp (mkConst ``Not) paramType) retType
      withLocalDeclD scopedName paramType fun bv => do
        -- register scoped variable in context to make it visible in inner proof
        let (_, mvarTmp) ← MVarId.intro1P $ ← mvar.assert scopedName paramType bv
        let mvar' ← runProof mvarTmp steps
        mvar'.withContext do
          -- hack to recover bv after changing contexts
          let lctx ← getLCtx
          let some ldecl1 := lctx.findFromUserName? scopedName |
            throwError "[scope]: lost bv"
          let some ldecl2 := lctx.findFromUserName? lastName |
            throwError "[scope]: did not find final proof in context"
          let lambda ← mkLambdaFVars #[.fvar ldecl1.fvarId] (.fvar ldecl2.fvarId)
          let pf := mkApp3 (mkConst ``scope) paramType retType lambda
          let (_, mvar'') ← MVarId.intro1P $ ← mvar'.assert name goalExpr pf
          return mvar''

partial def runProof (mvar: MVarId) (pf : List Step): TacticM MVarId := do
  pf.foldlM runStep mvar

end

def closeGoalWithCvc5Proof (pf: Cvc5Proof): TacticM Unit := do
  let goal ← getMainGoal
  let goal' ← runProof goal pf.steps
  goal'.withContext do
    let lctx ← getLCtx
    let some ldecl := lctx.findFromUserName? pf.lastName |
      throwError "final proof not defined in context"
    goal'.assign ldecl.value
    replaceMainGoal []

-- Testing

def cvc5Proof1 : Cvc5Proof := {
  steps := [.tac `pf "True" "exact True.intro"]
  lastName := `pf
}

def cvc5Proof2 : Cvc5Proof := {
  steps := [.thm `pf "True" `True.intro []]
  lastName := `pf
}

def cvc5Proof3 : Cvc5Proof := {
  steps := [ .intro `lean_a0
           , .thm `pf "True" `lean_a0 []
           ]
  lastName := `pf
}

def cvc5Proof4: Cvc5Proof := {
  steps := [ .intro `lean_a0
           , .thm `lean_s0 "Not ((P -> Q) -> Q)" ``notImplies2 ["lean_a0"]
           , .thm `lean_s1 "P -> Q" ``notImplies1 ["lean_s0"]
           , .thm `lean_s2 "Or (Not P) Q" ``impliesElim ["lean_s1"]
           , .thm `lean_s3 "P" ``notImplies1 ["lean_a0"]
           , .tac `lean_s4 "Q" "R2 lean_s2, lean_s3, P, [1, 0]"
           , .thm `lean_s5 "Not ((P -> Q) -> Q)" ``notImplies2 ["lean_a0"]
           , .thm `lean_s6 "Not Q" ``notImplies2 ["lean_s5"]
           , .thm `pf "False" ``contradiction ["lean_s4", "lean_s6"]
           ]
  lastName := `pf
}

def cvc5Proof5: Cvc5Proof := {
  steps := [ .intro `lean_a0
           , .scope `lean_a1 "P" "Q" `hp `inner_pf 
               [ .thm `inner_pf "Q" `lean_a0 [] ]
           , .thm `pf "¬ P ∨ Q" `lean_a1 []
           ]
  lastName := `pf
}

syntax (name := test) "test" term : tactic

@[tactic test] def evalTest : Tactic := fun stx =>
  withMainContext do
    let id ← stxToNat ⟨stx[1]⟩
    let pf ←
      match id with
      | 1 => pure cvc5Proof1
      | 2 => pure cvc5Proof2
      | 3 => pure cvc5Proof3
      | 4 => pure cvc5Proof4
      | 5 => pure cvc5Proof5
      | _ => throwError "unreachable"
    closeGoalWithCvc5Proof pf

example : True := by test 1

example : True := by test 2

example : False → False := by test 3

example (P Q : Prop) : Not (P → ((P → Q) → Q)) → False := by
  test 4

example (P Q : Prop) : Q → ¬ P ∨ Q := by
  test 5

