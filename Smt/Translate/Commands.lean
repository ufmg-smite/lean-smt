/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Smt.Data.Sexp
import Smt.Dsl.Sexp
import Smt.Translate.Term

namespace Smt.Translate

open Smt.Translate

/-- An SMT-LIBv2 command that we can emit. -/
inductive Command where
  | setLogic (l : String)
  | setOption (k : String) (v : String)
  | declareSort (nm : String) (arity : Nat)
  | defineSort (nm : String) (ps : List Term) (tm : Term)
  | declare (nm : String) (st : Term)
  | defineFun (nm : String) (ps : List (String × Term)) (cod : Term) (tm : Term) (rec : Bool)
  | assert (tm : Term)
  | checkSat
  | getModel
  | getProof
  | exit

namespace Command

open Lean Term

def defNat : Command := .defineSort "Nat" [] (symbolT "Int")

def defNatSub : Command :=
  .defineFun "Nat.sub" [("x", symbolT "Nat"), ("y", symbolT "Nat")] (symbolT "Nat")
    (Term.mkApp3 (symbolT "ite")
                 (Term.mkApp2 (symbolT "<") (symbolT "x") (symbolT "y"))
                 (literalT "0")
                 (Term.mkApp2 (symbolT "-") (symbolT "x") (symbolT "y")))
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

def cmdsAsQuery : List Command → String := .intercalate "\n" ∘ (.map toString)

end Smt.Translate.Command
