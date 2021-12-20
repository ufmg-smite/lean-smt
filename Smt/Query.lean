import Lean
import Smt.Graph
import Smt.Solver
import Smt.Transformer
import Smt.Constants

namespace Smt.Query

open Lean
open Lean.Expr
open Lean.Meta
open Smt
open Smt.Solver
open Smt.Term
open Smt.Constants
open Std

partial def buildDependencyGraph (es : List Expr) : MetaM (Graph Expr Unit) :=
  buildDependencyGraph' es Graph.empty
  where
    buildDependencyGraph' (es : List Expr) (g : Graph Expr Unit) :
      MetaM (Graph Expr Unit) := do
      let mut g := g
      for e in es do
        assert!(e.isConst ∨ e.isFVar)
        if ¬(g.contains e) then
          g := g.addVertex e
          trace[Smt.debug.query] "e: {e}"
          let et ← inferType e
          trace[Smt.debug.query] "et: {et}"
          let fvs := Util.getFVars et
          trace[Smt.debug.query] "fvs: {fvs}"
          for fv in fvs do
            if ¬(g.contains fv) then
              g ← buildDependencyGraph' [fv] g
            g := g.addEdge e fv ()
          let ucs := Util.getUnkownConsts (← Transformer.preprocessExpr et)
          trace[Smt.debug.query] "ucs: {ucs}"
          for uc in ucs do
            if ¬(g.contains uc) then
              g := g.addVertex uc
            g := g.addEdge e uc ()
            if uc.constName? == some `Nat.sub then
              let nat := mkConst `Nat
              if ¬(g.contains nat) then
                g := g.addVertex nat
              g := g.addEdge uc nat ()
            -- TODO: further process uc
      g

def natAssertBody (n : String) :=
  App (App (Symbol ">=") (Symbol n)) (Literal "0")

def processVertex (e : Expr) : StateT Solver MetaM Unit := do
  let mut solver ← get
  trace[Smt.debug.query] "e: {e}"
  match e with
  | const `Nat ..     => set (defNat solver); return
  | const `Nat.sub .. => set (defNatSub solver); return
  | _                 => ()
  let t ← inferType e
  let mut t ← inferType e
  if Util.hasMVars t then
    t ← whnf t
  trace[Smt.debug.query] "t: {t}"
  let s ← Transformer.exprToTerm t
  trace[Smt.debug.query] "s: {s}"
  let n ← match e with
  | fvar id .. => (← Lean.Meta.getLocalDecl id).userName.toString
  | const n .. => n.toString
  | _          => panic! ""
  let tt ← Lean.Meta.inferType t
  _ ← set (match tt with
    | sort l ..  => match l.toNat with
      | some 0 => assert solver s
      | some 1 => match t with
        | forallE ..    => declareFun solver n s
        | const `Nat .. => assert (declareConst solver n s) (natAssertBody n)
        | _             => declareConst solver n s
      | _      => solver
    | _ => solver)

def generateQuery (es : List Expr) (solver : Solver) : MetaM Solver := do
  trace[Smt.debug.query] "benchmark FVars: {es}"
  let g ← buildDependencyGraph es
  trace[Smt.debug.query] "Dependency Graph: {g}"
  let (_, solver) ← StateT.run (g.dfs processVertex) solver
  solver

end Smt.Query
