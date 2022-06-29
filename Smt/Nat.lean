/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.Nat

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | const `Nat.add ..                                => return symbolT "+"
  | const `Nat.mul ..                                => return symbolT "*"
  | const `Nat.div ..                                => return symbolT "div"
  | const `Nat.le ..                                 => return symbolT "<="
  | const `Nat.ge ..                                 => return symbolT ">="
  -- TODO: why is this not removed at unfoldProjInsts ?
  | app (app (const `GE.ge ..) (const `Nat ..) _) .. => return symbolT ">="
  | _                                                => return none

@[smtTranslator] def replaceNatLit : Translator
  | lit (.natVal n) .. => return literalT (toString n)
  | _                  => return none

/-- Removes casts of literals to `Nat` in `e`. For example, given
    `(app (app (app (OfNat.ofNat ..) ..) (LIT 0) ..) ..)`, this method removes
    all applications and returns just `(LIT 0)`. -/
@[smtTranslator] def removeOfNat : Translator
  | app (app (app (const ``OfNat.ofNat ..) ..) l ..) .. => applyTranslators! l
  | _                                                   => return none

/-- Replaces `Nat` constructors `Nat.zero` and `Nat.succ n` for with `0` and
    `(+ n 1)`. -/
@[smtTranslator] def replaceCtr : Translator
  | app (const ``Nat.succ ..) e _ => do
    let tmE ← applyTranslators! e
    return Term.mkApp2 (symbolT "+") tmE (literalT "1")
  | const ``Nat.zero ..           => return literalT "0"
  | _                             => return none

/-- Removes applications of `Nat.decLe` in `e`.
    TODO: replace by unfolding projections. -/
@[smtTranslator] def removeDecLe : Translator
  | app (app f (app (app (const ``Nat.decLe ..) ..) ..) ..) e .. => do
    let tmF ← applyTranslators! f
    let tmE ← applyTranslators! e
    return appT tmF tmE
  | _ => return none

/- Replaces quantified expressions over natural numbers for with versions that
    ensure the quantified variables are greater than or equal to 0. For
    example, given `∀ x : Nat, p(x)`, this method returns the expr
    `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[smtTranslator] def replaceForalls : Translator
  | e@(forallE n t@(const ``Nat ..) b d) => do
    if e.isArrow then return none
    Meta.withLocalDecl n d.binderInfo t fun x => do
      let tmB ← applyTranslators! (b.instantiate #[x])
      let tmGeqZero := Term.mkApp2 (symbolT ">=") (symbolT n.toString) (literalT "0")
      let tmProp := Term.mkApp2 (symbolT "=>") tmGeqZero tmB
      return forallT n.toString (symbolT "Int") tmProp
  | _ => return none

end Smt.Nat
