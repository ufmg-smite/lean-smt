/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.Prop

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | sort (.zero _) _          => return symbolT "Bool"
  | const `True ..            => return symbolT "true"
  | const `False ..           => return symbolT "false"
  | const `Not ..             => return symbolT "not"
  | const `And ..             => return symbolT "and"
  | const `Or ..              => return symbolT "or"
  | const `Iff ..             => return symbolT "="
  | app (const `Eq ..) ..     => return symbolT "="
  | app (const `Ne ..) ..     => return symbolT "distinct"
  | app (const `ite ..) ..    => return symbolT "ite"
  | _                         => return none

@[smtTranslator] def replaceExists : Translator
  | e@(app (app (const `Exists ..) ..) f _) => do
    let lam n t b d := f | throwError "unexpected predicate {f} in {e}"
    Meta.withLocalDecl n d.binderInfo t fun x => do
      let tmT ← applyTranslators! t
      let tmB ← applyTranslators! (b.instantiate #[x])
      return existsT n.toString tmT tmB
  | _                         => return none

@[smtTranslator] def replaceDecIte : Translator
  | app (app (app (const `ite ..) ..) e _) .. => do
    let tmE ← applyTranslators! e
    return appT (symbolT "ite") tmE
  | _                         => return none

/-- Replaces arrows with `Imp`. For example, given `(FORALL _ p q)`, this
    method returns `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the translation step. -/
@[smtTranslator] partial def translateImps : Translator
  | e@(forallE n t b d) => do
    -- TODO: replace the first check with proper final domain check
    if e.isArrow ∧ (← Meta.inferType t).isProp then
      let tmE ← applyTranslators! t
      let tmB ← Meta.withLocalDecl n d.binderInfo t fun x => applyTranslators! (b.instantiate #[x])
      return appT (appT (symbolT "=>") tmE) tmB
    return none
  | _ => return none

end Smt.Prop
