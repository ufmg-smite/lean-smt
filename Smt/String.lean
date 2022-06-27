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
open Smt.Translator

@[smtTranslator] def replaceConst : Translator
  | app (const `Char.ofNat ..) e ..    => applyTranslators! e
  | app (const `String.Pos.mk ..) e .. => applyTranslators! e
  | const `String.replace ..           => return Term.Symbol "str.replace_all"
  | const `String.length ..            => return Term.Symbol "str.len"
  | const `String.append ..            => return Term.Symbol "str.++"
  | _                                  => return none

@[smtTranslator] def replaceStrLit : Translator
  | lit (.strVal s) .. => return Term.Literal s!"\"{s}\""
  | _                  => return none

@[smtTranslator] def replaceStringGetOp : Translator
  | app (app (const `String.getOp ..) f _) e _ => do
    let tmF ← applyTranslators! f
    let tmE ← applyTranslators! e
    return Term.App (Term.Symbol "str.to_code") (Term.mkApp2 (Term.Symbol "str.at") tmF tmE)
  | _                                          => return none

@[smtTranslator] def replaceStringContains : Translator
  | app (app (const `String.contains ..) f _) e _ => do
    let tmF ← applyTranslators! f
    let tmE ← applyTranslators! e
    return Term.mkApp2 (Term.Symbol "str.contains") tmF (Term.App (Term.Symbol "str.from_code") tmE)
  | _                                             => return none

@[smtTranslator] def replaceStringLt : Translator
  | app (app (app (app (const `List.lt ..) ..) ..)
        (app (const `String.data ..) a _) _)
        (app (const `String.data ..) b _) _ => do
    let tmA ← applyTranslators! a
    let tmB ← applyTranslators! b
    return Term.mkApp2 (Term.Symbol "str.<") tmA tmB
  | _                                       => return none

end Smt.String
