/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Lean
import Smt.Graph
import Smt.Solver
import Smt.Transformer
import Smt.Constants

namespace Smt.Query

open Lean Expr Meta
open Constants Solver Term
open Std

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
      assert!(e.isConst ∨ e.isFVar ∨ e.isMVar)
      modify (·.addVertex e)
      if e.isConst then
        if e.constName! == `Nat then
          return
        if e.constName! == `Nat.sub then
          modify (·.addEdge e (mkConst `Nat) ())
          return
      trace[smt.debug.query] "e: {e}"
      let et ← inferType e
      trace[smt.debug.query] "et: {et}"
      let fvs := Util.getFVars et
      trace[smt.debug.query] "fvs: {fvs}"
      let ucs := Util.getUnkownConsts (← Transformer.preprocessExpr et)
      trace[smt.debug.query] "ucs: {ucs}"
      let cs := fvs ++ ucs
      -- Processes the children.
      for c in cs do
        buildDependencyGraph' c hs
        modify (·.addEdge e c ())
      -- If `e` is a function name in the list of hints, unfold it.
      if ¬(e.isConst ∧ hs.elem e ∧ ¬(← inferType et).isProp) then
        return
      match ← getUnfoldEqnFor? e.constName! with
      | some eqnThm =>
        let eqnInfo ← getConstInfo eqnThm
        let d := eqnInfo.type
        trace[smt.debug.query] "d: {d}"
        let dfvs := Util.getFVars d
        trace[smt.debug.query] "dfvs: {dfvs}"
        let ducs := Util.getUnkownConsts (← Transformer.preprocessExpr d)
        trace[smt.debug.query] "ducs: {ducs}"
        let dcs := dfvs ++ ducs
        for dc in dcs do
          buildDependencyGraph' dc hs
          modify (·.addEdge e dc ())
      | none        => pure ()
      return

def sortEndsWithNat : Term → Bool
  | Arrow _ t    => sortEndsWithNat t
  | Symbol "Nat" => true
  | _            => false

def natAssertBody (t : Term) :=
  App (App (Symbol ">=") t) (Literal "0")

/-- TODO: refactor to support functions as input (e.g., (Nat → Nat) → Nat). -/
def natConstAssert (n : String) (args : List Name) : Term → MetaM Term
  | Arrow i@(Symbol "Nat") t => do
    let id ← Lean.mkFreshId
    return (Forall id.toString i
                   (imp id.toString (← natConstAssert n (id::args) t)))
  | Arrow a t => do
    let id ← Lean.mkFreshId
    return (Forall id.toString a (← natConstAssert n (id::args) t))
  | _ => pure $ natAssertBody (applyList n args)
  where
    imp n t := App (App (Symbol "=>") (natAssertBody (Symbol n))) t
    applyList n : List Name → Term
      | [] => Symbol n
      | t :: ts => App (applyList n ts) (Symbol t.toString)

-- TODO: support recursive functions.
partial def toDefineFun (s : Solver) (e : Expr) : MetaM Solver := do
  let defn : Expr ← Meta.unfoldDefinition e
  pure (defineFun s id (← params defn) (← type (← Meta.inferType defn)) (← body defn))
  where
    id := if let const n .. := e then n.toString else panic! ""
    params : Expr → MetaM (List (String × Term))
      | lam n t e _ => do
        return (n.toString, (← Transformer.exprToTerm t)) :: (← params e)
      | _ => pure []
    type : Expr →  MetaM Term
      | forallE _ _ t _ => type t
      | t => Transformer.exprToTerm t
    body : Expr → MetaM Term
      | lam n t b d => Meta.withLocalDecl n d.binderInfo t (fun x => body (b.instantiate #[x]))
      | e => do return ← Transformer.exprToTerm e

partial def toDefineConst (s : Solver) (e : Expr) : MetaM Solver := do
  let defn : Expr ← Meta.unfoldDefinition e
  pure (defineConst s id (← type (← Meta.inferType defn)) (← body defn))
  where
    id := if let const n .. := e then n.toString else panic! ""
    type := Transformer.exprToTerm
    body : Expr → MetaM Term
      | lam n t b d => Meta.withLocalDecl n d.binderInfo t (fun x => body (b.instantiate #[x]))
      | e => do return ← Transformer.exprToTerm e

def processVertex (hs : List Expr) (e : Expr) : StateT Solver MetaM Unit := do
  let mut solver ← get
  trace[smt.debug.query] "e: {e}"
  match e with
  | const `Nat ..     => set (defNat solver); return
  | const `Nat.sub .. => set (defNatSub solver); return
  | _                 => pure ()
  let mut t ← inferType e
  if Util.hasMVars t then
    t ← whnf t
  trace[smt.debug.query] "t: {t}"
  let s ← Transformer.exprToTerm t
  trace[smt.debug.query] "s: {s}"
  let n ← match e with
  | fvar id .. => pure (← getLocalDecl id).userName.toString
  | const n .. => pure n.toString
  | _          => panic! ""
  trace[smt.debug.query] "here1"
  let tt ← inferType t
  trace[smt.debug.query] "here2"
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

def generateQuery (g : Expr) (hs : List Expr) (solver : Solver) : MetaM Solver :=
  traceCtx `smt.debug.generateQuery do
    trace[smt.debug.query] "Goal: {g}"
    trace[smt.debug.query] "Provided Hints: {hs}"
    let g ← buildDependencyGraph g hs
    trace[smt.debug.query] "Dependency Graph: {g}"
    let (_, solver) ← StateT.run (g.dfs $ processVertex hs) solver
    return solver

end Smt.Query
