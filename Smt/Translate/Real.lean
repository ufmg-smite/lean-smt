/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Recognizers
import Mathlib.Data.Real.Archimedean

import Smt.Translate

namespace Smt.Translate.Rat

open Translator Term

private def mkReal : Lean.Expr :=
  .const ``Real []

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Real _  => return symbolT "Real"
  | _                => return none

@[smt_translate] def translateInt : Translator := fun e => do
  if let some x := e.intFloorOf? mkReal then
    return appT (symbolT "to_int") (← applyTranslators! x)
  else
    return none

@[smt_translate] def translateReal : Translator := fun e => do
  if let some n := e.natLitOf? mkReal then
    return literalT s!"{n}.0"
  else if let some x := e.intCastOf? mkReal then
    return appT (symbolT "to_real") (← applyTranslators! x)
  else if let some x := e.negOf? mkReal then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some x := e.absOf? mkReal then
    return appT (symbolT "abs") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkReal mkReal then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkReal mkReal then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkReal mkReal then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkReal mkReal then
    return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkReal then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkReal then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkReal then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkReal then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Rat
