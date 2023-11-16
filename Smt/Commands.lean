/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Smt.Data.Sexp
import Smt.Dsl.Sexp
import Smt.Term

namespace Smt
open Smt

/-- An SMT-LIBv2 command that we can emit. -/
inductive Command where
  | setLogic (l : String)
  | setOption (k : String) (v : String)
  | declareSort (nm : String) (arity : Nat)
  | defineSort (nm : String) (ps : List Term) (tm : Term)
  | declare (nm : String) (st : Term)
  | declareFun (nm : String) (ps : List Term) (cod : Term)
  | defineFun (nm : String) (ps : List (String × Term)) (cod : Term) (tm : Term) (rec : Bool)
  | assert (tm : Term)
  | checkSat
  | getModel
  | getProof
  | exit

namespace Command

open Lean
open Term
open scoped Term.Notation

def defNat : Command := .defineSort "Nat" [] (`"Int")

def defNatSub : Command :=
  .defineFun "Nat.sub" [("x", `"Nat"), ("y", `"Nat")] (`"Nat")
    (`"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y"))
    false

open ToSexp in
protected def toSexp : Command → Sexp
  | .setLogic l                   => sexp!{(set-logic {l})}
  | .setOption k v                => sexp!{(set-option {s!":{k}"} {v})}
  | .assert val                   => sexp!{(assert {val})}
  | .declare nm st@(arrowT ..)    =>
    let sts := arrowToList st
    sexp!{(declare-fun {quoteSymbol nm} (...{sts.dropLast.map toSexp}) {sts.getLast!})}
  | .declare nm st                => sexp!{(declare-const {quoteSymbol nm} {st})}
  | .declareSort nm arity         =>
    sexp!{(declare-sort {quoteSymbol nm} {toString arity})}
  | .defineSort nm ps tm          =>
    sexp!{(define-sort {quoteSymbol nm} (...{ps.map toSexp}) {tm})}
  | .declareFun nm ps cod =>
    sexp!{(declare-fun {quoteSymbol nm} (...{ps.map toSexp}) {cod})}
  | .defineFun nm ps cod tm false =>
    sexp!{(define-fun {quoteSymbol nm} {paramsToSexp ps} {cod} {tm})}
  | .defineFun nm ps cod tm true  =>
    sexp!{(define-fun-rec {quoteSymbol nm} {paramsToSexp ps} {cod} {tm})}
  | .checkSat                     => sexp!{(check-sat)}
  | .getModel                     => sexp!{(get-model)}
  | .getProof                     => sexp!{(get-proof)}
  | .exit                         => sexp!{(exit)}
where
  arrowToList : Term → List Term
    | arrowT d c => d :: arrowToList c
    | s          => [s]
  paramToSexp (p : String × Term) : Sexp := sexp!{({quoteSymbol p.fst} {p.snd})}
  paramsToSexp (ps : List (String × Term)) : Sexp := sexp!{(...{ps.map paramToSexp})}

instance : ToSexp Command := ⟨Command.toSexp⟩

instance : ToString Command := ⟨toString ∘ ToSexp.toSexp⟩

def cmdsAsQuery : List Command → String := .intercalate "\n" ∘ (.map toString) ∘ .reverse

end Command
end Smt
