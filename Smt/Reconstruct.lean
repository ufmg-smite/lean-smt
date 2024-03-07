/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5
import Qq
import Std

import Smt.Attribute

namespace Smt

open Lean
open Attribute

structure Reconstruct.state where
  termCache : HashMap cvc5.Term Expr
  proofCache : HashMap cvc5.Proof Expr
  count : Nat
  trusts : Array cvc5.Proof
  mainGoal : MVarId
  currGoal : MVarId
  currAssums : Array Expr
  skipedGoals : Array MVarId

abbrev ReconstructM := StateT Reconstruct.state MetaM

abbrev SortReconstructor := cvc5.Sort → ReconstructM (Option Expr)

abbrev TermReconstructor := cvc5.Term → ReconstructM (Option Expr)

abbrev ProofReconstructor := cvc5.Proof → ReconstructM (Option Expr)

namespace Reconstruct

private unsafe def getReconstructorsUnsafe (n : Name) (rcons : Type) : MetaM (List (rcons × Name)) := do
  let env ← getEnv
  let names := ((smtExt.getState env).findD n {}).toList
  let mut reconstructors := []
  for name in names do
    let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConst rcons Options.empty name
    reconstructors := (fn, name) :: reconstructors
  return reconstructors

@[implemented_by getReconstructorsUnsafe]
opaque getReconstructors (n : Name) (rcons : Type) : MetaM (List (rcons × Name))

def reconstructSort (s : cvc5.Sort) : ReconstructM Expr := do
  let rs ← getReconstructors ``SortReconstructor SortReconstructor
  go rs s
where
  go (rs : List (SortReconstructor × Name)) (s : cvc5.Sort) : ReconstructM Expr := do
    for (r, n) in rs do
      if let some e ← r s then
        trace[smt.debug.reconstruct.sort] "{s} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct sort {s} with kind {repr s.getKind}"

def traceReconstructTerm (t : cvc5.Term) (r : Except Exception Expr) : ReconstructM MessageData :=
  return m!"{t} ↦ " ++ match r with
    | .ok e    => m!"{e}"
    | .error _ => m!"{bombEmoji}"

def reconstructTerm : cvc5.Term → ReconstructM Expr := withTermCache fun t =>
  withTraceNode `smt.debug.reconstruct (traceReconstructTerm t) do
    let rs ← getReconstructors ``TermReconstructor TermReconstructor
    go rs t
where
  withTermCache (r : cvc5.Term → ReconstructM Expr) (t : cvc5.Term) : ReconstructM Expr := do
    match (← get).termCache.find? t with
    -- TODO: cvc5's global bound variables mess up the cache. Find a fix.
    | some e => if e.hasFVar then reconstruct r t else return e
    | none   => reconstruct r t
  reconstruct r t := do
    let e ← r t
    modify fun state => { state with termCache := state.termCache.insert t e }
    return e
  go (rs : List (TermReconstructor × Name)) (t : cvc5.Term) : ReconstructM Expr := do
    for (r, n) in rs do
      if let some e ← r t then
        trace[smt.debug.reconstruct.term] "{t} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct term {t} with kind {repr t.getKind}"

def withProofCache (r : cvc5.Proof → ReconstructM Expr) (p : cvc5.Proof) : ReconstructM Expr := do
  match (← get).proofCache.find? p with
  | some e => (← get).currGoal.withContext do
    if (← getLCtx).containsFVar e then return e else reconstruct r p
  | none   => reconstruct r p
where
  reconstruct r p := do
    let e ← r p
    modify fun state => { state with proofCache := state.proofCache.insert p e }
    return e

def incCount : ReconstructM Nat :=
  modifyGet fun state => (state.count, { state with count := state.count + 1 })

def withAssums (as : Array Expr) (k : ReconstructM α) : ReconstructM α := do
  modify fun state => { state with currAssums := state.currAssums ++ as }
  let r ← k
  modify fun state => { state with currAssums := state.currAssums.shrink (state.currAssums.size - as.size) }
  return r

def skipStep (mv : MVarId) : ReconstructM Unit := mv.withContext do
  let state ← get
  let t ← Meta.mkForallFVars state.currAssums (← mv.getType)
  let mv' ← state.mainGoal.withContext (Meta.mkFreshExprMVar t)
  let e := mkAppN mv' state.currAssums
  set { state with skipedGoals := state.skipedGoals.push mv'.mvarId! }
  mv.assignIfDefeq e

def getCurrGoal : ReconstructM MVarId :=
  get >>= (pure ·.currGoal)

def setCurrGoal (mv : MVarId) : ReconstructM Unit :=
  modify fun state => { state with currGoal := mv }

def addThm (type : Expr) (val : Expr) : ReconstructM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let (fv, mv) ← (← mv.assert name type val).intro1P
    trace[smt.debug.reconstruct.proof] "have {name} : {type} := {val}"
    setCurrGoal mv
    return .fvar fv

def addTac (type : Expr) (tac : MVarId → MetaM Unit) : ReconstructM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let mv' ← Meta.mkFreshExprMVar type
    tac mv'.mvarId!
    let (fv, mv) ← (← mv.assert name type mv').intro1P
    trace[smt.debug.reconstruct.proof] "have {name} : {type} := by {mv'}"
    setCurrGoal mv
    return .fvar fv

def addTrust (type : Expr) (pf : cvc5.Proof) : ReconstructM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let mv' ← Meta.mkFreshExprMVar type
    skipStep mv'.mvarId!
    let (fv, mv) ← (← mv.assert name type mv').intro1P
    trace[smt.debug.reconstruct.proof] m!"have {name} : {type} := sorry"
    trace[smt.debug.reconstruct.proof]
      m!"rule : {repr pf.getRule}\npremises : {pf.getChildren.map (·.getResult)}\nargs : {pf.getArguments}\nconclusion : {pf.getResult}"
    modify fun state => { state with trusts := state.trusts.push pf }
    setCurrGoal mv
    return .fvar fv

partial def reconstructProof : cvc5.Proof → ReconstructM Expr := withProofCache fun pf => do
  let rs ← getReconstructors ``ProofReconstructor ProofReconstructor
  go rs pf
where
  go (rs : List (ProofReconstructor × Name)) (pf : cvc5.Proof) : ReconstructM Expr := do
    for (r, _) in rs do
      if let some e ← r pf then
        return e
    _ ← pf.getChildren.mapM reconstructProof
    let type ← reconstructTerm pf.getResult
    addTrust type pf

end Reconstruct

def traceReconstructProof (r : Except Exception (FVarId × MVarId × List MVarId)) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Qq in
partial def reconstructProof (mv : MVarId) (pf : cvc5.Proof) : MetaM (FVarId × MVarId × List MVarId) :=
  withTraceNode `smt.debug.reconstruct traceReconstructProof do
  let Prod.mk (p : Q(Prop)) state ← (Reconstruct.reconstructTerm (pf.getResult)).run ⟨{}, {}, 0, #[], mv, mv, #[], #[]⟩
  let Prod.mk (h : Q(True → $p)) (.mk _ _ _ _ _ mv _ mvs) ← (Reconstruct.reconstructProof pf).run state
  let ⟨fv, mv, _⟩ ← mv.replace h.fvarId! q($h trivial) q($p)
  return (fv, mv, mvs.toList)

open cvc5 in
def traceProve (r : Except Exception (Except SolverError Proof)) : MetaM MessageData :=
  return match r with
  | .ok (.ok _) => m!"{checkEmoji}"
  | _           => m!"{bombEmoji}"

open cvc5 in
def prove (query : String) (timeout : Option Nat) : MetaM (Except SolverError cvc5.Proof) :=
  withTraceNode `smt.debug.prove traceProve do Solver.run do
    if let .some timeout := timeout then
      Solver.setOption "tlimit" (toString (1000*timeout))
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "simplification" "none"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "produce-models" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parse query
    let r ← Solver.checkSat
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        trace[smt.debug.reconstruct] (← Solver.proofToString ps[0])
        return ps[0]
    throw (self := instMonadExcept _ _) (SolverError.user_error "something went wrong")

syntax (name := reconstruct) "reconstruct" str : tactic

open Lean.Elab Tactic in
@[tactic reconstruct] def evalReconstruct : Tactic := fun stx =>
  withMainContext do
    let some query := stx[1].isStrLit? | throwError "expected string"
    let r ← prove query none
    match r with
      | .error e => logInfo (repr e)
      | .ok pf =>
        let (_, mv, mvs) ← reconstructProof (← getMainGoal) pf
        replaceMainGoal (mv :: mvs)

end Smt
