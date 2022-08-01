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
  | defineFun (nm : String) (ps : List (String × Term)) (cod : Term) (tm : Term) (rec : Bool)
  | assert (tm : Term)
  | checkSat
  | getModel
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
  | .assert val                   => sexp!{(assert {toSexp val})}
  | .declare nm st@(arrowT ..)    =>
    let sts := arrowToList st
    sexp!{(declare-fun {quoteSymbol nm} (...{sts.init.map toSexp}) {toSexp sts.getLast!})}
  | .declare nm st                => sexp!{(declare-const {quoteSymbol nm} {toSexp st})}
  | .declareSort nm arity         =>
    sexp!{(declare-sort {quoteSymbol nm} {String.mk (Nat.toDigits 10 arity)})}
  | .defineSort nm ps tm          =>
    sexp!{(define-sort {quoteSymbol nm} (...{ps.map toSexp}) {toSexp tm})}
  | .defineFun nm [] cod tm _     =>
    sexp!{(define-const {quoteSymbol nm} {toSexp cod} {toSexp tm})}
  | .defineFun nm ps cod tm false =>
    sexp!{(define-fun {quoteSymbol nm} {paramsToSexp ps} {toSexp cod} {toSexp tm})}
  | .defineFun nm ps cod tm true  =>
    sexp!{(define-fun-rec {quoteSymbol nm} {paramsToSexp ps} {toSexp cod} {toSexp tm})}
  | .checkSat                     => sexp!{(check-sat)}
  | .getModel                     => sexp!{(get-model)}
  | .exit                         => sexp!{(exit)}
where
  arrowToList : Term → List Term
    | arrowT d c => d :: arrowToList c
    | s          => [s]
  paramToSexp (p : String × Term) : Sexp := sexp!{({quoteSymbol p.fst} {toSexp p.snd})}
  paramsToSexp (ps : List (String × Term)) : Sexp := sexp!{(...{ps.map paramToSexp})}

instance : ToSexp Command := ⟨Command.toSexp⟩

instance : ToString Command := ⟨toString ∘ ToSexp.toSexp⟩

instance : ToString (List Command) := ⟨.intercalate "\n" ∘ (.map toString) ∘ .reverse⟩

instance : ToMessageData (List Command) := ⟨toMessageData ∘ toString⟩

end Command
end Smt
