/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Qq

import Mathlib.Data.Real.Archimedean

import Smt.Translate.Translator

namespace Smt.Translate.Rat

open Qq
open Translator Term

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(Real)  => return symbolT "Real"
  | _         => return none

@[smt_translate] def translateInt : Translator := fun (e : Q(Int)) => match e with
  | ~q(⌊($x : Real)⌋) => return appT (symbolT "to_int") (← applyTranslators! x)
  | _                => return none

@[smt_translate] def translateReal : Translator := fun (e : Q(Real)) => match e with
  | ~q((($x : Int) : Real)) => return appT (symbolT "to_real") (← applyTranslators! x)
  | ~q(@OfNat.ofNat _ _ (@instOfNat _ _ _ instNatAtLeastTwo)) =>
    return if let some n := (e.getArg! 1).natLit? then literalT s!"{n}.0" else none
  | ~q(0)       => return (literalT "0.0")
  | ~q(1)       => return (literalT "1.0")
  | ~q(-$x)     => return appT (symbolT "-") (← applyTranslators! x)
  | ~q($x + $y) => return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x - $y) => return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x * $y) => return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x / $y) => return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  | _           => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($x : Real) = ⌊$x⌋) => return appT (symbolT "is_int") (← applyTranslators! x)
  | ~q(($x : Real) < $y) => return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Real) ≤ $y) => return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Real) ≥ $y) => return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Real) > $y) => return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  | _                    => return none

end Smt.Translate.Rat
