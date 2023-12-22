/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.«Prop»

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | sort .zero           => return symbolT "Bool"
  | const `True _        => return symbolT "true"
  | const `False _       => return symbolT "false"
  | const `Not _         => return symbolT "not"
  | const `And _         => return symbolT "and"
  | const `Or _          => return symbolT "or"
  | const `Iff _         => return symbolT "="
  | app (const `Eq _) _  => return symbolT "="
  | app (const `Ne _) _  => return symbolT "distinct"
  | _                    => return none

@[smtTranslator] def replaceExists : Translator
  | e@(app (app (const `Exists _) _) f) => do
    let lam n t b bi := f | throwError "unexpected predicate {f} in {e}"
    Meta.withLocalDecl n bi t fun x => do
      let tmT ← applyTranslators! t
      let tmB ← applyTranslators! (b.instantiate #[x])
      return existsT n.toString tmT tmB
  | _ => return none

/- @Eq.rec : {α : Sort u_2} →
  {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} → motive a (_ : a = a) → {a_1 : α} → (t : a = a_1) → motive a_1 t -/
@[smtTranslator] def replaceEqRec : Translator
  | app (app (app (app (app (app (const `Eq.rec _) _) _) _) e) _) _ => do
    trace[smt.debug.replaceEqRec] "found eq_rec body : {e}"
    applyTranslators? e
  | _ => return none

def emitIte (cond : Expr) (t : TranslationM Term) (f : TranslationM Term)
    : TranslationM (Option Term) := do
  return mkApp3 (symbolT "ite") (← applyTranslators! cond) (← t) (← f)

@[smtTranslator] def replaceIte : Translator
  /- @ite : {α : Sort u_1} → (c : Prop) → [h : Decidable c] → α → α → α -/
  | app (app (app (app (app (const `ite _) _) c) _inst) a) b =>
    emitIte c (applyTranslators! a) (applyTranslators! b)
  /- @dite : {α : Sort u_1} → (c : Prop) → [h : Decidable c] → (c → α) → (¬c → α) → α -/
  | app (app (app (app (app (const `dite _) _) c) _inst) a) b => do
    -- Note: we assume that the translation of both branches erases any uses
    -- of the condition proposition.
    emitIte c
      (Meta.lambdaTelescope a fun args bd => applyTranslators! (bd.instantiate args))
      (Meta.lambdaTelescope b fun args bd => applyTranslators! (bd.instantiate args))
  | _ => return none

-- Local `have` proofs are encoded as `let_fun`. Remove them.
@[smtTranslator] def replaceHave : Translator := fun e => do
  let some e := annotation? `let_fun e | return none
  if !e.appFn!.isLambda then return none
  Meta.lambdaTelescope e.appFn! fun args bd => do
    trace[smt.debug.replacePropLetFun] "found let_fun {e}"
    let #[arg] := args | return none
    trace[smt.debug.replacePropLetFun] "arg : {arg}"
    if !(← Meta.inferType (← Meta.inferType arg)).isProp then return none
    trace[smt.debug.replacePropLetFun] "translating {bd.instantiate #[arg]}"
    applyTranslators? (bd.instantiate #[arg])

/-- Replaces arrows with `Imp`. For example, given `(FORALL _ p q)`, this
    method returns `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the translation step. -/
@[smtTranslator] partial def translateImps : Translator
  | e@(forallE n t b bi) => do
    -- TODO: replace the first check with proper final domain check
    if e.isArrow ∧ (← Meta.inferType t).isProp then
      let tmE ← applyTranslators! t
      let tmB ← Meta.withLocalDecl n bi t fun x => applyTranslators! (b.instantiate #[x])
      return appT (appT (symbolT "=>") tmE) tmB
    return none
  | _ => return none

end Smt.«Prop»
