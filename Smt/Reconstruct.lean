/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5
import Qq

import Smt.Attribute

namespace Smt

open Lean
open Attribute

structure Reconstruct.Context where
  /-- The user names of the variables in the local context. -/
  userNames : Std.HashMap String FVarId := {}
  /-- Whether to enable native components for proof reconstruction. Speeds up normalization and
      reduction proof steps. However, it adds the Lean compiler to the trusted code base. -/
  native : Bool := false

structure Reconstruct.State where
  termCache : Std.HashMap cvc5.Term Expr := {}
  proofCache : Std.HashMap cvc5.Proof Expr := {}
  count : Nat := 0
  currAssums : Array Expr := #[]
  skippedGoals : Array MVarId := #[]

abbrev ReconstructM := ReaderT Reconstruct.Context (StateT Reconstruct.State MetaM)

abbrev SortReconstructor := cvc5.Sort → ReconstructM (Option Expr)

abbrev TermReconstructor := cvc5.Term → ReconstructM (Option Expr)

abbrev ProofReconstructor := cvc5.Proof → ReconstructM (Option Expr)

namespace Reconstruct

def useNative : ReconstructM Bool :=
  read >>= pure ∘ (·.native)

private unsafe def getReconstructorsUnsafe (n : Name) (rcons : Type) : MetaM (List (rcons × Name)) := do
  let env ← getEnv
  let names := ((smtExt.getState env).getD n {}).toList
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
        trace[smt.reconstruct.sort] "{s} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct sort {s} with kind {s.getKind}"

def reconstructSortLevelAndSort (s : cvc5.Sort) : ReconstructM (Level × Expr) := do
  let t ← reconstructSort s
  let .sort u ← Meta.inferType t | throwError "expected a sort, but got\n{t}"
  return ⟨u, t⟩

def withNewTermCache (k : ReconstructM α) : ReconstructM α := do
  let termCache := (← get).termCache
  modify fun state => { state with termCache := {} }
  let r ← k
  modify fun state => { state with termCache := termCache }
  return r

def traceReconstructTerm (t : cvc5.Term) (r : Except Exception Expr) : ReconstructM MessageData :=
  return m!"{t} ↦ " ++ match r with
    | .ok e    => m!"{e}"
    | .error _ => m!"{bombEmoji}"

def reconstructTerm : cvc5.Term → ReconstructM Expr := withTermCache fun t => do
  withTraceNode ((`smt.reconstruct.term).str t.getKind.toString) (traceReconstructTerm t) do
    let rs ← getReconstructors ``TermReconstructor TermReconstructor
    go rs t
where
  withTermCache (r : cvc5.Term → ReconstructM Expr) (t : cvc5.Term) : ReconstructM Expr := do
    match (← get).termCache[t]? with
    -- TODO: cvc5's global bound variables mess up the cache. Find a better fix.
    | some e => return e
    | none   => reconstruct r t
  reconstruct r t := do
    let e ← r t
    modify fun state => { state with termCache := state.termCache.insert t e }
    return e
  go (rs : List (TermReconstructor × Name)) (t : cvc5.Term) : ReconstructM Expr := do
    for (r, n) in rs do
      if let some e ← r t then
        trace[smt.reconstruct.term] "{t} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct term {t} with kind {t.getKind}"

open Qq in
def reconstructTerms {u} {α : Q(Type $u)} (ts : Array cvc5.Term) : ReconstructM Q(List $α) :=
  let f := fun t ys => do
    let a : Q($α) ← reconstructTerm t
    return q($a :: $ys)
  ts.foldrM f q([])

def withNewProofCache (k : ReconstructM α) : ReconstructM α := do
  let proofCache := (← get).proofCache
  modify fun state => { state with proofCache := {} }
  let r ← k
  modify fun state => { state with proofCache := proofCache }
  return r

def withProofCache (r : cvc5.Proof → ReconstructM Expr) (pf : cvc5.Proof) : ReconstructM Expr := do
  match (← get).proofCache[pf]? with
  | some e => return e
  | none   => reconstruct r pf
where
  reconstruct r pf := do
    let e ← r pf
    modify fun state => { state with proofCache := state.proofCache.insert pf e }
    return e

def incCount : ReconstructM Nat :=
  modifyGet fun state => (state.count, { state with count := state.count + 1 })

def withAssums (as : Array Expr) (k : ReconstructM α) : ReconstructM α := do
  modify fun state => { state with currAssums := state.currAssums ++ as }
  let r ← k
  modify fun state => { state with currAssums := state.currAssums.take (state.currAssums.size - as.size) }
  return r

def findAssumWithType? (t : Expr) : ReconstructM (Option Expr) := do
  for a in (← get).currAssums.reverse do
    let t' ← a.fvarId!.getType
    if t' == t then
      return some a
  return none

def skipStep (mv : MVarId) : ReconstructM Unit := mv.withContext do
  let state ← get
  let t ← Meta.mkForallFVars state.currAssums (← mv.getType)
  let ctx := state.currAssums.foldr (fun e ctx => ctx.erase e.fvarId!) (← getLCtx)
  let mv' ← Meta.withLCtx ctx (← Meta.getLocalInstances) (Meta.mkFreshExprMVar t)
  let e := mkAppN mv' state.currAssums
  set { state with skippedGoals := state.skippedGoals.push mv'.mvarId! }
  mv.assign e

def addThm (type : Expr) (val : Expr) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  mv.mvarId!.assign val
  trace[smt.reconstruct.proof] "have {name} : {type} := {val}"
  return mv

def addTac (type : Expr) (tac : MVarId → MetaM Unit) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  tac mv.mvarId!
  trace[smt.reconstruct.proof] "have {name} : {type} := {mv}"
  return mv

def addTrust (type : Expr) (pf : cvc5.Proof) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  skipStep mv.mvarId!
  trace[smt.reconstruct.proof] m!"have {name} : {type} := sorry"
  trace[smt.reconstruct.proof]
    m!"rule : {pf.getRule}\npremises : {pf.getChildren.map (·.getResult)}\nargs : {pf.getArguments}\nconclusion : {pf.getResult}"
  return mv

def traceReconstructStep (r : Except Exception Expr) : ReconstructM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

partial def reconstructProof : cvc5.Proof → ReconstructM Expr := withProofCache fun pf => do
  let rs ← getReconstructors ``ProofReconstructor ProofReconstructor
  go rs pf
where
  go (rs : List (ProofReconstructor × Name)) (pf : cvc5.Proof) : ReconstructM Expr :=
  withTraceNode ((`smt.reconstruct.proof).str pf.getRule.toString) traceReconstructStep do
    for (r, _) in rs do
      if let some e ← r pf then
        return e
    _ ← pf.getChildren.mapM reconstructProof
    let type ← reconstructTerm pf.getResult
    addTrust type pf

end Reconstruct

def traceReconstructProof (r : Except Exception (List Expr × List Expr × Expr × Expr × List MVarId)) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Qq in
partial def reconstructProof (pf : cvc5.Proof) (ctx : Reconstruct.Context) :
  MetaM (List Expr × List Expr × Expr × Expr × List MVarId) :=
  withTraceNode `smt.reconstruct.proof traceReconstructProof do
  let (dfns, state) ← (pf.getArguments.toList.mapM Reconstruct.reconstructTerm).run ctx {}
  let (ps, state) ← (pf.getChildren[0]!.getArguments.toList.mapM Reconstruct.reconstructTerm).run ctx state
  let ((p : Q(Prop)), state) ← (Reconstruct.reconstructTerm (pf.getResult)).run ctx state
  let (h, ⟨_, _, _, _, mvs⟩) ← (Reconstruct.reconstructProof pf).run ctx state
  if dfns.isEmpty then
    let h : Q(True → $p) ← pure h
    return (dfns, ps, p, q($h trivial), mvs.toList)
  else
    return (dfns, ps, p, h, mvs.toList)

open cvc5 in
def traceSolve (r : Except Exception (Except SolverError Proof)) : MetaM MessageData :=
  return match r with
  | .ok (.ok _) => m!"{checkEmoji}"
  | _           => m!"{bombEmoji}"

open cvc5 in
def solve (query : String) (timeout : Option Nat) : MetaM (Except Error cvc5.Proof) :=
  profileitM Exception "simp" {} do
  withTraceNode `smt.solve traceSolve do Solver.run (← TermManager.new) do
    if let .some timeout := timeout then
      Solver.setOption "tlimit" (toString (1000*timeout))
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "simplification" "none"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "cegqi-midpoint" "true"
    Solver.setOption "produce-models" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parseCommands query
    let r ← Solver.checkSat
    trace[smt.solve] m!"result: {r}"
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        trace[smt.solve] "proof:\n{← Solver.proofToString ps[0]}"
        return ps[0]
    throw (self := instMonadExceptOfMonadExceptOf _ _) (Error.error s!"Expected unsat, got {r}")

syntax (name := reconstruct) "reconstruct" str : tactic

open Lean.Elab Tactic in
@[tactic reconstruct] def evalReconstruct : Tactic := fun stx =>
  withMainContext do
    let some query := stx[1].isStrLit? | throwError "expected string"
    let r ← solve query none
    match r with
      | .error e => logInfo (repr e)
      | .ok pf =>
        let (_, _, p, hp, mvs) ← reconstructProof pf ⟨(← getUserNames), false⟩
        let mv ← Tactic.getMainGoal
        let mv ← mv.assert (Name.num `s 0) p hp
        let (_, mv) ← mv.intro1
        replaceMainGoal (mv :: mvs)
where
  getUserNames : MetaM (Std.HashMap String FVarId) := do
    let lCtx ← getLCtx
    return lCtx.getFVarIds.foldl (init := {}) fun m fvarId =>
      m.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString fvarId

end Smt
