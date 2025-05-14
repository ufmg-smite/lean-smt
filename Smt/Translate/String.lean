/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.String

open Lean Expr
open Translator Term

private def mkString : Expr :=
  .const ``String []

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``String _ => return symbolT "String"
  | _                 => return none

@[smt_translate] def translateInt : Translator := fun e => do
  if let some s := e.app1? ``String.length then
    return appT (symbolT "str.len") (← applyTranslators! s)
  else
    return none

@[smt_translate] def translateString : Translator := fun e => do
  if let .lit (.strVal s) := e then
    return literalT s!"\"{s}\""
  else if let some (z, x, y) := e.app3? ``String.replace then
    return mkApp3 (symbolT "str.replace_all") (← applyTranslators! z) (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hAppendOf? mkString mkString then
    return mkApp2 (symbolT "str.++") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkString then
    return mkApp2 (symbolT "str.<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkString then
    return mkApp2 (symbolT "str.>") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.String
