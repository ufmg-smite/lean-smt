/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Int

open Translator Term

private def mkInt : Lean.Expr :=
  .const ``Int []

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Int _ => return symbolT "Int"
  | _              => return none

@[smt_translate] def translateInt : Translator := fun e => do
  if let some n := e.natLitOf? mkInt then
    return literalT (toString n)
  else if let some x := e.negOf? mkInt then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkInt mkInt then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkInt mkInt then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkInt mkInt then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkInt mkInt then
    return mkApp2 (symbolT "div") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hModOf? mkInt mkInt then
    return mkApp2 (symbolT "mod") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkInt then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkInt then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkInt then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkInt then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Int
