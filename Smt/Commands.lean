/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas, Wojciech Nawrocki
-/

import Smt.Solver
import Smt.Term

namespace Smt

/-- An SMT-LIBv2 command that we can emit. -/
inductive Command where
  | assert (tm : Term)
  | declare (nm : String) (st : Term)
  | declareSort (nm : String) (arity : Nat)
  | defineSort (nm : String) (ps : List Term) (tm : Term)
  | defineFun (nm : String) (ps : List (String × Term)) (cod : Term) (tm : Term) (rec : Bool)

namespace Command

open Lean
open Term
open scoped Term.Notation

def defNat : Command := .defineSort "Nat" [] (`"Int")

def defNatSub : Command :=
  .defineFun "Nat.sub" [("x", `"Nat"), ("y", `"Nat")] (`"Nat")
    (`"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y"))
    false

def sortEndsWithNat : Term → Bool
  | arrowT _ t    => sortEndsWithNat t
  | symbolT "Nat" => true
  | _             => false

def natAssertBody (t : Term) : Term :=
  mkApp2 (symbolT ">=") t (literalT "0")

variable [Monad m] [MonadNameGenerator m]

/-- TODO: refactor to support functions as input (e.g., (Nat → Nat) → Nat). -/
def natConstAssert (n : String) (args : List Name) : Term → m Term
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

def emitCommand (s : Solver) (cmd : Command) : m Solver := do
  let mut s := s
  match cmd with
  | .assert val                   => s := s.assert val
  | .declare nm st@(arrowT ..)    => s := s.declareFun nm st
  | .declare nm st                => s := s.declareConst nm st
  | .declareSort nm arity         => s := s.declareSort nm arity
  | .defineSort nm ps tm          => s := s.defineSort nm ps tm
  | .defineFun nm ps cod tm true  => s := s.defineFunRec nm ps cod tm
  | .defineFun nm ps cod tm false => s := s.defineFun nm ps cod tm
  match cmd with
  | .declare nm st =>
    if sortEndsWithNat st then
      s := s.assert (← natConstAssert nm [] st)
  | .defineFun nm ps cod _ _ =>
    if sortEndsWithNat cod then
      let tmArrow := ps.foldr (init := cod) fun (_, tp) acc => arrowT tp acc
      s := s.assert (← natConstAssert nm [] tmArrow)
  | _ => pure ()
  return s

end Command
end Smt
