import Smt
import Smt.Real

/-!
# Checking cvc5 proofs of SMT-LIB files

`Checker.check path` runs cvc5 on the SMT-LIB file `path` through lean-cvc5, with the solver
options of the `smt` tactic, reconstructs the proof with lean-smt, and sends the resulting theorem
to the kernel. The three phases are timed separately and reported as

```
[time] solve: <ms>
[time] reconstruct: <ms>
[time] kernel: <ms>
[result] ok | error | trusted steps
```

The design follows abdoo8080/lean-cpc-checker. Use it from a driver file (see
`scripts/check_smt2.sh`, which generates one):

```
import Checker
run_cmd Checker.check "problem.smt2" (coarse := false)
```

`coarse := true` asks cvc5 for the monolithic `ARITH_COVERINGS_UNIV` rule instead of the
fine-grained coverings rules (the `+coarse` option of the tactic).
-/

open Lean Qq

namespace Checker

def printlnAndFlush [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

/-- The outcome of running cvc5 on a query. -/
inductive SolveResult where
  | unsat (pf : cvc5.Proof) (fvs : Array cvc5.Term)
  | sat
  | unknown (reason : String)
  | error (e : cvc5.Error)

/-- The script without its `check-sat`, `get-*` and `exit` commands, so that the checker can run
`check-sat` itself and see the result. Commands are assumed to start at a line beginning. -/
def stripCheckSat (query : String) : String :=
  let dropped := ["(check-sat)", "(exit)", "(get-model)", "(get-proof)", "(get-unsat-core)"]
  "\n".intercalate <| query.splitOn "\n" |>.filter fun l => !dropped.contains l.trim

/-- Runs cvc5 on `query` with the options of the `smt` tactic. On unsat, returns the proof and the
declared constants. -/
def solve (query : String) (coarse : Bool) (solverOptions : List (String × String) := []) :
    IO SolveResult := do
  let r ← cvc5.run (m := IO) do
    let tm ← cvc5.TermManager.new
    let slv ← cvc5.Solver.new tm
    for (opt, val) in Smt.defaultSolverOptions do
      slv.setOption opt val
    slv.setOption "nl-cov-univ-coarse-proof" (toString coarse)
    -- overrides of the tactic's options, e.g. ("simplification", "batch") to let cvc5 substitute
    -- equalities so that problems with a constraint mixing variables become univariate
    for (opt, val) in solverOptions do
      slv.setOption opt val
    let (_, fvs) ← slv.parseCommands (stripCheckSat query)
    let res ← slv.checkSat
    if res.isUnsat then
      let ps ← slv.getProof
      if h : 0 < ps.size then
        return SolveResult.unsat ps[0] fvs
      return SolveResult.error (cvc5.Error.error "expected a proof, got none")
    else if res.isSat then
      return SolveResult.sat
    else
      return SolveResult.unknown res.getUnknownExplanation.toString
  match r with
  | .ok r => return r
  | .error e => return .error e

/-- Declares the SMT-LIB constants as local variables, with their sorts reconstructed by lean-smt,
and runs `k` with the map from SMT-LIB symbols to those variables. -/
def withDeclaredFuns [Inhabited α] (vs : Array cvc5.Term)
    (k : Std.HashMap String Expr → Array Expr → MetaM α) : MetaM α := do
  let ctx : Smt.Reconstruct.Context := {}
  let decls : Array (Name × (Array Expr → MetaM Expr)) := vs.map fun v =>
    (Name.mkSimple v.getSymbol!, fun _ => do
      let (t, _) ← ((Smt.Reconstruct.reconstructSort v.getSort).run ctx).run {}
      return t)
  Meta.withLocalDeclsD decls fun xs => do
    let mut names : Std.HashMap String Expr := {}
    for (v, x) in vs.zip xs do
      names := names.insert v.getSymbol! x
    k names xs

inductive Status where
  | ok
  /-- the reconstruction left trusted steps (closed by `sorry`) -/
  | trusted
  | kernelError
deriving Inhabited

instance : ToString Status where
  toString
    | .ok => "ok"
    | .trusted => "trusted steps"
    | .kernelError => "error"

/-- Reconstructs `pf` and checks the theorem with the kernel. Returns the reconstruction time, the
kernel time, and the status. -/
def checkProof (pf : cvc5.Proof) (fvs : Array cvc5.Term) (native : Bool) :
    MetaM (Nat × Nat × Status) := do
  let t0 ← IO.monoMsNow
  let (type, value, trusted) ← withDeclaredFuns fvs fun names xs => do
    let ctx : Smt.Reconstruct.Context := { userNames := names, native }
    let (_, _, type, value, mvs) ← Smt.reconstructProof pf ctx
    for mv in mvs do
      let p : Q(Prop) ← mv.getType
      mv.assign q(sorry : $p)
    let value ← instantiateMVars value
    let value ← Meta.mkLambdaFVars xs value
    let type ← Meta.mkForallFVars xs type
    return (type, value, !mvs.isEmpty)
  let t1 ← IO.monoMsNow
  let decl := Declaration.thmDecl { name := `checked, levelParams := [], type, value }
  let env := (← getEnv).toKernelEnv
  let opts ← getOptions
  -- `lazyPure` forces the kernel call to run here, between the two timestamps; a pure `let`
  -- could be floated by the compiler to its use site below.
  let r ← IO.lazyPure fun _ => env.addDecl opts decl
  let t2 ← IO.monoMsNow
  match r with
  | .error e =>
    logError m!"kernel: {e.toMessageData (← getOptions)}"
    return (t1 - t0, t2 - t1, .kernelError)
  | .ok _ =>
    return (t1 - t0, t2 - t1, if trusted then .trusted else .ok)

/-- Solves and checks the SMT-LIB file at `path`, printing the times and the status. -/
def check (path : String) (coarse := false) (native := false)
    (solverOptions : List (String × String) := []) : Elab.Command.CommandElabM Unit := do
  let query ← IO.FS.readFile path
  let t0 ← IO.monoMsNow
  let r ← solve query coarse solverOptions
  let t1 ← IO.monoMsNow
  printlnAndFlush s!"[time] solve: {t1 - t0}ms"
  match r with
  | .error e => printlnAndFlush s!"[result] solver error: {e}"
  | .sat => printlnAndFlush "[result] sat"
  | .unknown r => printlnAndFlush s!"[result] unknown: {r}"
  | .unsat pf fvs =>
    Elab.Command.runTermElabM fun _ => do
      let (tr, tk, status) ← checkProof pf fvs native
      printlnAndFlush s!"[time] reconstruct: {tr}ms"
      printlnAndFlush s!"[time] kernel: {tk}ms"
      printlnAndFlush s!"[result] {status}"

end Checker
