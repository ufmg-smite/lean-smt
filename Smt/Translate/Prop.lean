/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Prop

open Lean Expr
open Translator Term

private def mkProp : Lean.Expr :=
  .sort 0

@[smt_translate] def translateType : Translator := fun e => match e with
  | .sort 0        => return symbolT "Bool"
  | _              => return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let .const ``True _ := e then
    return symbolT "true"
  else if let .const ``False _ := e then
    return symbolT "false"
  else if let some p := e.not? then
    return appT (symbolT "not") (← applyTranslators! p)
  else if let some (p, q) := e.and? then
    return mkApp2 (symbolT "and") (← applyTranslators! p) (← applyTranslators! q)
  else if let some (p, q) := e.or? then
    return mkApp2 (symbolT "or") (← applyTranslators! p) (← applyTranslators! q)
  else if let some (_, x, y) := e.eq? then
    return mkApp2 (symbolT "=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (_, x, y) := e.ne? then
    return mkApp2 (symbolT "distinct") (← applyTranslators! x) (← applyTranslators! y)
  -- Implication is more expensive than other connectives, because it is
  -- represented as a (non-)dependent arrow in Lean. So we keep it last.
  else if let some (p, q) ← e.imp? then
    return mkApp2 (symbolT "=>") (← applyTranslators! p) (← applyTranslators! q)
  else
    return none

@[smt_translate] def translateExists : Translator
  | e@(app (app (const `Exists _) _) f) => do
    let lam n t b bi := f | throwError "unexpected predicate {f} in {e}"
    withScopedName n b fun n => do
      let tmT ← applyTranslators! t
      let tmB ← Meta.withLocalDecl n bi t (translateBody b)
      return existsT n.toString tmT tmB
  | _ => return none
where
  translateBody (b : Expr) (x : Expr) : TranslationM Term := do
    modify fun s => { s with localFVars := s.localFVars.insert x.fvarId! }
    let tmB ← applyTranslators! (b.instantiate #[x])
    modify fun s => { s with localFVars := s.localFVars.erase x.fvarId! }
    return tmB

/- @Eq.rec : {α : Sort u_2} →
  {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} → motive a (_ : a = a) → {a_1 : α} → (t : a = a_1) → motive a_1 t -/
@[smt_translate] def translateEqRec : Translator
  | app (app (app (app (app (app (const `Eq.rec _) _) _) _) e) _) _ => do
    trace[smt.translateEqRec] "found eq_rec body : {e}"
    applyTranslators? e
  | _ => return none

def emitIte (cond : Expr) (t : TranslationM Term) (f : TranslationM Term)
    : TranslationM (Option Term) := do
  return mkApp3 (symbolT "ite") (← applyTranslators! cond) (← t) (← f)

@[smt_translate] def translateIte : Translator
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
@[smt_translate] def translateHave : Translator := fun e => do
  let some (_, _, _, e) := letFun? e | return none
  if !e.appFn!.isLambda then return none
  Meta.lambdaTelescope e.appFn! fun args bd => do
    trace[smt.translatePropLetFun] "found let_fun {e}"
    let #[arg] := args | return none
    trace[smt.translatePropLetFun] "arg : {arg}"
    if !(← Meta.inferType (← Meta.inferType arg)).isProp then return none
    trace[smt.translatePropLetFun] "translating {bd.instantiate #[arg]}"
    applyTranslators? (bd.instantiate #[arg])

end Smt.Translate.Prop
