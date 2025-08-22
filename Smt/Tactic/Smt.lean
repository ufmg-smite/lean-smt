/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Dsl.Sexp
import Smt.Reconstruct
import Smt.Reconstruct.Prop.Lemmas
import Smt.Translate.Query
import Smt.Preprocess
import Smt.Util
import Smt.Auto

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

/-- Configuration options for the SMT tactic. -/
structure Config where
  /-- The timeout for the SMT solver in seconds. -/
  timeout : Option Nat := .none
  /-- Whether to enable native components for proof reconstruction. Speeds up normalization and
      reduction proof steps. However, it adds the Lean compiler to the trusted code base. -/
  native : Bool := false
  /-- Whether to preprocess the query before sending it to the SMT solver. -/
  preprocess : Bool := true
  /-- Whether to monomorphize the Lean goal before invoking the SMT solver. -/
  mono : Bool := false
  /-- Whether to trust the result of the SMT solver. Closes the current goal with a `sorry` if the
      SMT solver returns `unsat`. **Warning**: use with caution, as this may lead to unsoundness.
      Additionally adds the translation from Lean to SMT to the trusted code base, which is not
      always sound. -/
  trust : Bool := false
  /-- Just show the SMT query without invoking a solver. Useful for debugging. -/
  showQuery : Bool := false
deriving Inhabited, Repr

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      if ← pure !(isNonEmpty localDecl.type) <&&> Meta.isProp localDecl.type then
        result := result.push localDecl.fvarId
  return result
where
  isNonEmpty (e : Expr) : Bool :=
  match_expr e with
  | Nonempty _ => true
  | _ => false

def genUniqueFVarNames : MetaM (Std.HashMap FVarId String × Std.HashMap String FVarId) := do
  let lCtx ← getLCtx
  let st : NameSanitizerState := { options := {}}
  let (lCtx, _) := (lCtx.sanitizeNames st).run
  return lCtx.getFVarIds.foldl (init := ({}, {})) fun (m₁, m₂) fvarId =>
    let m₁ := m₁.insert fvarId (lCtx.getRoundtrippingUserName? fvarId).get!.toString
    let m₂ := m₂.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString fvarId
    (m₁, m₂)

def prepareSmtQuery (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs fvNames

def withProcessedHints (mv : MVarId) (hints : Auto.InputHints') (k : MVarId → List Expr → MetaM α) : MetaM α := do
  let mut hs := hints.lemmas.map (·.proof)
  if hints.lctxhyps then
    hs := hs ++ (← getPropHyps).toList.map Expr.fvar
  go mv hs.toList [] k
where
  go (mv : MVarId) (hs : List Expr) (fvs : List Expr) (k : MVarId → List Expr → MetaM α): MetaM α := do
    match hs with
    | [] => k mv fvs
    | h :: hs =>
      if h.isFVar || h.isConst then
        go mv hs (h :: fvs) k
      else
        let mv ← mv.assert (← mkFreshId) (← Meta.inferType h) h
        let ⟨fv, mv⟩ ← mv.intro1
        go mv hs (.fvar fv :: fvs) k

def withMono (mv : MVarId) (hs : Auto.InputHints') (k : MVarId → List Expr → MetaM α) : MetaM α := do
  let (mv, _) ← Auto.mono' `smt mv hs #[] #[]
  let hs ← mv.withContext (return (← Smt.getPropHyps).toList.map Expr.fvar)
  trace[smt] "goal: {mv}"
  k mv hs

def smt (cfg : Config) (mv : MVarId) (hs : Auto.InputHints') : MetaM (List MVarId) := mv.withContext do
  -- 0. Create a duplicate goal to preserve the original goal.
  let mv₁ := (← Meta.mkFreshExprMVar (← mv.getType)).mvarId!
  -- 1. Process the hints passed to the tactic.
  (if cfg.mono then withMono else withProcessedHints) mv₁ hs fun mv₂ hs => mv₂.withContext do
  -- 2. Preprocess the hypotheses and goal.
  let (hs, mv₂) ← if cfg.preprocess then Preprocess.elimIff mv₂ hs else pure (hs, mv₂)
  mv₂.withContext do
  let goalType : Q(Prop) ← mv₂.getType
  -- 3. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  let cmds ← prepareSmtQuery hs (← mv₂.getType) fvNames₁
  let cmds := .setLogic "ALL" :: cmds
  if cfg.showQuery then
    logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
    -- Return original goal.
    return [mv]
  else
    trace[smt] "goal: {goalType}"
    trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- 4. Run the solver.
  let res ← solve (Command.cmdsAsQuery cmds) cfg.timeout
  -- trace[smt] "\nresult: {res}"
  match res with
  | .error e =>
    -- 5a. Print error reason.
    trace[smt] "\nerror reason:\n{repr e}\n"
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
  | .ok pf =>
    if cfg.trust then
      -- 5b. Trust the result by admitting original goal.
      mv.admit true
      return []
    -- 5c. Reconstruct proof.
    let ctx := { userNames := fvNames₂, native := cfg.native }
    let (_, ps, p, hp, mvs) ← reconstructProof pf ctx
    let mv₂ ← mv₂.assert (← mkFreshId) p hp
    let ⟨_, mv₂⟩ ← mv₂.intro1
    let mut gs ← mv₂.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ps.dropLast q(Prop), goalType])
    mv₂.withContext (gs.forM (·.assumption))
    mv.assign (.mvar mv₁)
    return mvs

namespace Tactic

syntax smtStar := "*"

syntax smtHints := (" [" withoutPosition((smtStar <|> term),*,?) "]")?

open Lean.Parser.Tactic in
/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the current goal. However, that is not always enough:
```lean
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` and `hpq` required to prove the theorem. To
pass hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
```
The tactic then generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(declare-const p Bool)
(assert p)
(assert (=> p q))
(check-sat)
```
The tactic also supports the `*` wildcard hint, which means "all hypotheses".
So, the following also works:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [*]
```
The tactic can be configured with additional options. For example, to set a
timeout of 1 second for the SMT solver, use:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt (timeout := .some 1) [*]
```
Please take a look at the `Smt.Config` structure for more options.
-/
syntax (name := smt) "smt " optConfig smtHints : tactic

open Lean.Parser.Tactic in
/-- `smt_show` is short-hand for `smt +showQuery`. -/
macro "smt_show " c:optConfig h:smtHints : tactic => do
  let `(optConfig| $cs*) := c | Macro.throwUnsupported
  match h with
  | `(smtHints| )        => `(tactic| (smt +showQuery $cs*))
  | `(smtHints| [$hs,*]) => `(tactic| (smt +showQuery $cs* [$hs,*]))
  | _                    => Macro.throwUnsupported

declare_config_elab elabConfig Smt.Config

def elabHints : TSyntax `smtHints → TacticM (Auto.InputHints')
  | `(smtHints| [ $[$hs],* ]) => withMainContext do
    hs.foldrM (init := ⟨#[], #[], false⟩) fun h acc => do
      if h.getKind == ``Smt.Tactic.smtStar then
        return { acc with lctxhyps := true }
      let h ← Auto.Prep.elabLemma ⟨h⟩ (.leaf s!"❰{h}❱")
      return { acc with lemmas := acc.lemmas.push h }
  | `(smtHints| ) => return ⟨#[], #[], false⟩
  | _ => throwUnsupportedSyntax

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let mvs ← Smt.smt (← elabConfig stx[1]) (← Tactic.getMainGoal) (← elabHints ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs

end Smt.Tactic
