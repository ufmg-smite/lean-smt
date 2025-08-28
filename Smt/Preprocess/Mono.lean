/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Auto.Tactic
import Smt.Preprocess.Basic

namespace Auto

open Lean Elab Embedding.Lam

def DTr.contains (self : DTr) (other : DTr) : Bool :=
  if self == other then true
  else match self with
    | .leaf _ => false
    | .node _ dtrs => dtrs.attach.any fun ⟨dtr, _⟩ => dtr.contains other

structure InputHints' where
  lemmas   : Array Lemma := #[]
  lemdbs   : Array Name  := #[]
  lctxhyps : Bool        := false
deriving Inhabited, BEq

/--
  From a user-provided term `stx`, produce a lemma
-/
def Prep.elabLemma' (e : Expr) (deriv : DTr) : MetaM Lemma := do
  -- abstract any remaining mvars:
  let e ← instantiateMVars e
  let abstres ← Auto.abstractMVars e
  let e := abstres.expr
  let paramNames := abstres.paramNames
  return Lemma.mk ⟨e, ← Meta.inferType e, deriv⟩ paramNames

def Prep.elabDefEq' (name : Name) : MetaM (Array Lemma) := do
  match (← getEnv).find? name with
  | some (.recInfo val) =>
    -- Generate definitional equation for recursor
    addRecAsLemma val
  | some (.defnInfo val) =>
    -- Generate definitional equation for (possibly recursive) declaration
    match ← Meta.getEqnsFor? name with
    | some eqns => eqns.mapIdxM fun i eq => do
      -- TODO: create mvs for implicit arguments as well.
      let us ← Meta.mkFreshLevelMVarsFor (.defnInfo val)
      elabLemma' (.const eq us) (.leaf s!"defeq {i} {name}")
    | none => return #[]
  | some (.axiomInfo _)  => return #[]
  | some (.thmInfo _)    => return #[]
  -- If we have inductively defined propositions, we might
  --   need to add constructors as lemmas
  | some (.ctorInfo _)   => return #[]
  | some (.opaqueInfo _) => throwError "{decl_name%} :: Opaque constants cannot be provided as lemmas"
  | some (.quotInfo _)   => throwError "{decl_name%} :: Quotient constants cannot be provided as lemmas"
  | some (.inductInfo _) => throwError "{decl_name%} :: Inductive types cannot be provided as lemmas"
  | none => throwError "{decl_name%} :: Unknown constant {name}"

def collectUserLemmas' (exprs : Array Expr) : MetaM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let mut lemmas := #[]
    for expr in exprs do
      let ⟨⟨proof, type, deriv⟩, params⟩ ← Prep.elabLemma' expr (.leaf s!"❰{expr}❱")
      if ← Prep.isNonemptyInhabited type then
        throwError "invalid lemma {type}, lemmas should not be inhabitation facts"
      else if ← Meta.isProp type then
        lemmas := lemmas.push ⟨⟨proof, ← instantiateMVars type, deriv⟩, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
    return lemmas

def collectHintDBLemmas' (names : Array Name) : MetaM (Array Lemma) := do
  let mut hs : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut ret : Array Lemma := #[]
  for name in names do
    let .some db ← findLemDB name
      | throwError "unknown lemma database {name}"
    let lemNames ← db.toHashSet
    for lname in lemNames do
      if !hs.contains lname then
        hs := hs.insert lname
        ret := ret.push (← Lemma.ofConst lname (.leaf s!"lemdb {name} {lname}"))
  return ret

def collectDefeqLemmas' (names : Array Name) : MetaM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let lemmas ← names.flatMapM Prep.elabDefEq'
    lemmas.mapM (fun (⟨⟨proof, type, deriv⟩, params⟩ : Lemma) => do
      let type ← instantiateMVars type
      return ⟨⟨proof, type, deriv⟩, params⟩)

def checkDuplicatedFact' (exprs : Array Lemma) : MetaM Unit :=
  let n := exprs.size
  for i in [0:n] do
    for j in [i+1:n] do
      if exprs[i]? == exprs[j]? then
        throwError "Auto does not accept duplicated input terms"

def checkDuplicatedLemmaDB' (names : Array Name) : MetaM Unit :=
  let n := names.size
  for i in [0:n] do
    for j in [i+1:n] do
      if names[i]? == names[j]? then
        throwError "Auto does not accept duplicated lemma databases"

def collectAllLemmas' (inputHints : InputHints') (unfoldInfos : Array Prep.ConstUnfoldInfo)
  (defeqNames : Array Name) (ngoalAndBinders : Array FVarId) :
  -- The first `Array Lemma` are `Prop` lemmas
  -- The second `Array Lemma` are Inhabitation facts
  MetaM (Array Lemma × Array Lemma) := do
  let unfoldInfos ← Prep.topoSortUnfolds unfoldInfos
  let startTime ← IO.monoMsNow
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoalAndBinders
  let lctxLemmas ← lctxLemmas.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact' inputHints.lemmas
  checkDuplicatedLemmaDB' inputHints.lemdbs
  let userLemmas := inputHints.lemmas ++ (← collectHintDBLemmas' inputHints.lemdbs)
  let userLemmas ← userLemmas.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided terms:" userLemmas
  let defeqLemmas ← collectDefeqLemmas' defeqNames
  let defeqLemmas ← defeqLemmas.mapM (unfoldConstAndprepReduceDefeq unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided defeq hints:" defeqLemmas
  trace[auto.tactic] "Preprocessing took {(← IO.monoMsNow) - startTime}ms"
  let inhFacts ← Inhabitation.getInhFactsFromLCtx
  let inhFacts ← inhFacts.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Inhabitation lemmas :" inhFacts
  return (lctxLemmas ++ userLemmas ++ defeqLemmas, inhFacts)

def createInhHyps : FVarId × DTr → MetaM (Option Meta.Hypothesis) := fun (fv, dtr) => do
  let s := match dtr with
    | .leaf s => s
    | .node s _ => s
  if s.startsWith "nonemptyOfAtom" || s.startsWith "lctxInh" then
    let userName ← mkFreshUserName `inst
    let type ← Meta.mkAppM ``Nonempty #[← fv.getType]
    let value ← Meta.mkAppOptM ``Nonempty.intro #[← fv.getType, Expr.fvar fv]
    return some { userName, type, value }
  return none

def mono' (declName? : Option Name) (mv : MVarId) (hints : InputHints') (unfoldInfos : Array Prep.ConstUnfoldInfo) (defeqNames : Array Name) := do
  let (goalBinders, newGoal) ← mv.intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{declName?} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  absurd.withContext do
    let (lemmas, inhFacts) ← collectAllLemmas' hints unfoldInfos defeqNames (goalBinders.push ngoal)
    let (proof, (mvarId, dtrs)) ← runMono declName? lemmas inhFacts
    mvarId.withContext do
      let hs ← dtrs.filterMapM createInhHyps
      let f (acc : MessageData) (dtr : FVarId × DTr) :=
        acc ++ m!"\n<{Expr.fvar dtr.fst}> = <{ToString.toString dtr.snd}>"
      let message : MessageData := dtrs.foldl f m!""
      trace[smt.preprocess] "dtrs: {message}"
      let (_, mv) ← mvarId.assertHypotheses hs
      absurd.assign proof
      return (mv, dtrs)

namespace Tactic

/-- Parse `hints` to an array of `Term`, which is still syntax -/
def parseHints' : TSyntax ``hints → Tactic.TacticM InputHints'
| `(hints| [ $[$hs],* ]) => do
  let mut exprs := #[]
  let mut lemdbs := #[]
  let mut lctxhyps := false
  let elems ← hs.mapM parseHintElem
  for elem in elems do
    match elem with
    | .term t => exprs := exprs.push (← Prep.elabLemma t (.leaf s!"❰{t}❱"))
    | .lemdb db => lemdbs := lemdbs.push db
    | .lctxhyps => lctxhyps := true
  return ⟨exprs, lemdbs, lctxhyps⟩
| `(hints| ) => return ⟨#[], #[], true⟩
| _ => throwUnsupportedSyntax

syntax (name := mono') "mono' " hints (uord)* : tactic

open Lean Elab Tactic in
@[tactic mono'] def evalMono' : Tactic
  | `(mono' | mono' $hints $[$uords]*) => withMainContext do
    let hints ← parseHints' hints
    let (unfoldInfos, defeqNames) ← parseUOrDs uords
    let (mv, _) ← Auto.mono' (← Elab.Term.getDeclName?) (← Tactic.getMainGoal) hints unfoldInfos defeqNames
    Tactic.replaceMainGoal [mv]
  | _ => throwUnsupportedSyntax

end Auto.Tactic

namespace Smt.Preprocess

open Lean

open Auto in
def hintsToAutoHints (hs : Array Expr) : MetaM (Std.HashMap DTr Expr × InputHints' × Array Prep.ConstUnfoldInfo × Array Name) := do
  let lemmas ← hs.mapM inferLemma
  let map := .ofList (lemmas.map (fun l => (l.deriv, l.proof))).toList
  return (map, ⟨lemmas, #[], false⟩, #[], #[])
where
  inferLemma (e : Expr) : MetaM Lemma := do
    let paramNames ← getLevelParamNames e
    return Lemma.mk ⟨e, ← Meta.inferType e, (.node "smtHint" #[.leaf s!"{e}"])⟩ paramNames
  getLevelParamNames {ω : Type} {m} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m] (e : Expr) : m (Array Name) := do
    let ((), names) ← (e.forEach getLevelParamName).run (m := m) {}
    return names.toArray
  getLevelParamName {m} [Monad m] (e : Expr) : StateT (Std.HashSet Name) m Unit := do
    match e with
    | .const _ lvls =>
      let names := lvls.filterMap fun lvl => do
        let .param name := lvl | none
        some name
      modify fun s => s.insertMany names
    | _ => return

def mono (mv : MVarId) (hs : Array Expr) : MetaM Result := do
  let (invMap, hints, unfoldInfos, defeqNames) ← hintsToAutoHints hs
  let (mv, dtrs) ← Auto.mono' `smt mv hints unfoldInfos defeqNames
  let map := dtrs.foldl (init := {}) fun map (fv, dtr) =>
    let usedHints := invMap.filter (fun k _ => dtr.contains k)
    map.insert (.fvar fv) usedHints.valuesArray
  let hs ← mv.withContext (return (← getPropHyps).map Expr.fvar)
  trace[smt.preprocess] "goal: {mv}"
  return { map, hs, mv }

end Smt.Preprocess
