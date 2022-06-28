/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Lean
import Smt.Constants
import Smt.Graph
import Smt.Solver
import Smt.Translator
import Smt.Util

namespace Smt.Query

open Lean Expr Meta
open Constants Solver Term

-- TODO: move all `Nat` hacks in this file to `Nat.lean`.

partial def buildDependencyGraph (g : Expr) (hs : List Expr) :
  MetaM (Graph Expr Unit) := StateT.run' (s := Graph.empty) do
  buildDependencyGraph' g hs
  for h in hs do
    buildDependencyGraph' h hs
  get
  where
    buildDependencyGraph' (e : Expr) (hs : List Expr) :
       StateT (Graph Expr Unit) MetaM Unit := do
      if (← get).contains e then
        return
      if !(e.isConst ∨ e.isFVar ∨ e.isMVar) then
        throwError "failed to build graph, unexpected expression{indentD e}\nof kind {e.ctorName}"
      modify (·.addVertex e)
      if e.isConst then
        if e.constName! == `Nat then
          return
        if e.constName! == `Nat.sub then
          modify (·.addEdge e (mkConst `Nat) ())
          return
      trace[smt.debug.query] "e: {e}"
      let et ← inferType e
      let et ← instantiateMVars et
      trace[smt.debug.query] "et: {et}"
      let fvs := Util.getFVars et
      trace[smt.debug.query] "fvs: {fvs}"
      -- TODO(WN): we already invoke translation during graph construction,
      -- we should memoize it to avoid wasted work.
      let ucs ← Translator.getUnknownConstants et
      let ucs := ucs.fold (init := []) fun acc nm => mkConst nm :: acc
      trace[smt.debug.query] "ucs: {ucs}"
      let cs := fvs ++ ucs
      -- Processes the children.
      for c in cs do
        buildDependencyGraph' c hs
        modify (·.addEdge e c ())
      -- If `e` is a function name in the list of hints, unfold it.
      if ¬(e.isConst ∧ hs.elem e ∧ ¬(← inferType et).isProp) then
        return
      match ← getUnfoldEqnFor? e.constName! (nonRec := true) with
      | some eqnThm =>
        let eqnInfo ← getConstInfo eqnThm
        let d := eqnInfo.type
        trace[smt.debug.query] "d: {d}"
        let dfvs := Util.getFVars d
        trace[smt.debug.query] "dfvs: {dfvs}"
        let ducs ← Translator.getUnknownConstants et
        let ducs := ducs.fold (init := []) fun acc nm => mkConst nm :: acc
        trace[smt.debug.query] "ducs: {ducs}"
        let dcs := dfvs ++ ducs
        for dc in dcs do
          buildDependencyGraph' dc hs
          modify (·.addEdge e dc ())
      | none        => pure ()
      return

def sortEndsWithNat : Term → Bool
  | arrowT _ t    => sortEndsWithNat t
  | symbolT "Nat" => true
  | _             => false

def natAssertBody (t : Term) : Term :=
  mkApp2 (symbolT ">=") t (literalT "0")

/-- TODO: refactor to support functions as input (e.g., (Nat → Nat) → Nat). -/
def natConstAssert (n : String) (args : List Name) : Term → MetaM Term
  | arrowT i@(symbolT "Nat") t => do
    let id ← Lean.mkFreshId
    return (forallT id.toString i
                   (imp id.toString (← natConstAssert n (id::args) t)))
  | arrowT a t => do
    let id ← Lean.mkFreshId
    return (forallT id.toString a (← natConstAssert n (id::args) t))
  | _ => pure $ natAssertBody (applyList n args)
  where
    imp n t := appT (appT (symbolT "=>") (natAssertBody (symbolT n))) t
    applyList n : List Name → Term
      | [] => symbolT n
      | t :: ts => appT (applyList n ts) (symbolT t.toString)

-- TODO: support mutually recursive functions.
partial def toDefineFun (s : Solver) (e : Expr) : MetaM Solver := do
  let some eqnThm ← getUnfoldEqnFor? (nonRec := true) e.constName!
    | throwError "failed to retrieve equation theorem"
  let eqnInfo ← getConstInfo eqnThm
  let d := eqnInfo.type
  let mutRecFuns := ConstantInfo.all (← getConstInfo e.constName!)
  trace[smt.debug.query] "mutually recursive functions with {e}: {mutRecFuns}"
  -- TODO: Replace by `DefinitionVal.isRec` check when it gets added to Lean
  -- core.
  if mutRecFuns.length > 1 then
    throwError "mutually recursive functions are not yet supported"
  if Util.countConst d e.constName! > 1 then
    pure (defineFunRec s id (← params d) (← type (← inferType e)) (← body d))
  else
    pure (defineFun s id (← params d) (← type (← inferType e)) (← body d))
  where
    id := if let const n .. := e then n.toString else panic! ""
    params : Expr → MetaM (List (String × Term))
      | forallE n t e _ => do
        return (n.toString, (← Translator.translateExpr' t)) :: (← params e)
      | _ => pure []
    type : Expr →  MetaM Term
      | forallE _ _ t _ => type t
      | t => Translator.translateExpr' t
    /-- Given an equation theorm of the form `∀ x₁ ⬝⬝⬝ xₙ, n x₁ ⬝⬝⬝ xₙ = body`,
        this function instantiates all occurances of `x₁ ⬝⬝⬝ xₙ` in `body` and
        converts the resulting `Expr` into an equivalent SMT `Term`.  -/
    body : Expr → MetaM Term
      | forallE n t b d                          =>
        Meta.withLocalDecl n d.binderInfo t (fun x => body (b.instantiate #[x]))
      | app (app (app (const `Eq ..) ..) ..) e _ => Translator.translateExpr' e
      | e                                        =>
        throwError "Error: unexpected equation theorem: {e}"

partial def toDefineConst (s : Solver) (e : Expr) : MetaM Solver := do
  let defn : Expr ← Meta.unfoldDefinition e
  pure (defineConst s id (← type (← Meta.inferType defn)) (← body defn))
  where
    id := if let const n .. := e then n.toString else panic! ""
    type := Translator.translateExpr'
    body : Expr → MetaM Term
      | lam n t b d => Meta.withLocalDecl n d.binderInfo t (fun x => body (b.instantiate #[x]))
      | e => do return ← Translator.translateExpr' e

def processVertex (hs : List Expr) (e : Expr) : StateT Solver MetaM Unit := do
  let mut solver ← get
  trace[smt.debug.query] "e: {e}"
  match e with
  | const `Nat ..     => set (defNat solver); return
  | const `Nat.sub .. => set (defNatSub solver); return
  | _                 => pure ()
  let t ← inferType e
  let t ← instantiateMVars t
  trace[smt.debug.query] "t: {t}"
  let s ← Translator.translateExpr' t
  trace[smt.debug.query] "s: {s}"
  let n ← match e with
  | fvar id .. => pure (← getLocalDecl id).userName.toString
  | const n .. => pure n.toString
  | _          => panic! ""
  let tt ← inferType t
  match tt with
    | sort l ..  => match l.toNat with
      | some 0 => solver := assert solver s
      | some 1 => match t with
        | sort ..       => solver := declareConst solver n s
        | forallE ..    =>
          if hs.elem e then
            solver ← toDefineFun solver e
          else
            solver := (declareFun solver n s)
            if sortEndsWithNat s then
              solver := assert solver (← natConstAssert n [] s)
        | const id ..    =>
          if hs.elem e then
            solver ← toDefineConst solver e
          else
            solver := declareConst solver n s
            if id == `Nat then
              solver := assert solver (← natConstAssert n [] s)
        | _             => pure ()
      | _      => pure ()
    | _ => pure ()
  _ ← set solver

def generateQuery (goal : Expr) (hs : List Expr) (solver : Solver) : MetaM Solver :=
  traceCtx `smt.debug.generateQuery do
    trace[smt.debug.query] "Goal: {← inferType goal}"
    trace[smt.debug.query] "Provided Hints: {hs}"
    let g ← buildDependencyGraph goal hs
    trace[smt.debug.query] "Dependency Graph: {g}"
    let (_, solver) ← StateT.run (g.dfs $ processVertex hs) solver
    return solver

end Smt.Query
