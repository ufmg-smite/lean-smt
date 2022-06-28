/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.String

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | app (const `Char.ofNat ..) e ..    => applyTranslators! e
  | app (const `String.Pos.mk ..) e .. => applyTranslators! e
  | const `String.replace ..           => return symbolT "str.replace_all"
  | const `String.length ..            => return symbolT "str.len"
  | const `String.append ..            => return symbolT "str.++"
  | _                                  => return none

@[smtTranslator] def replaceStrLit : Translator
  | lit (.strVal s) .. => return literalT s!"\"{s}\""
  | _                  => return none

@[smtTranslator] def replaceStringGetOp : Translator
  | app (app (const `String.getOp ..) f _) e _ => do
    let tmF ← applyTranslators! f
    let tmE ← applyTranslators! e
    return appT (symbolT "str.to_code") (mkApp2 (symbolT "str.at") tmF tmE)
  | _                                          => return none

@[smtTranslator] def replaceStringContains : Translator
  | app (app (const `String.contains ..) f _) e _ => do
    let tmF ← applyTranslators! f
    let tmE ← applyTranslators! e
    return mkApp2 (symbolT "str.contains") tmF (appT (symbolT "str.from_code") tmE)
  | _                                             => return none

@[smtTranslator] def replaceStringLt : Translator
  | app (app (app (app (const `List.lt ..) ..) ..)
        (app (const `String.data ..) a _) _)
        (app (const `String.data ..) b _) _ => do
    let tmA ← applyTranslators! a
    let tmB ← applyTranslators! b
    return mkApp2 (symbolT "str.<") tmA tmB
  | _                                       => return none

end Smt.String
