/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Qq

import Smt.Translate

namespace Smt.Translate.Int

open Qq
open Translator Term

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(Int) => return symbolT "Int"
  | _       => return none

@[smt_translate] def translateInt : Translator := fun (e : Q(Int)) => match e with
  | ~q(OfNat.ofNat $n) => return if let some n := n.natLit? then literalT (toString n) else none
  | ~q(-$x)     => return appT (symbolT "-") (← applyTranslators! x)
  | ~q($x + $y) => return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x - $y) => return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x * $y) => return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x / $y) => return mkApp2 (symbolT "div") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x % $y) => return mkApp2 (symbolT "mod") (← applyTranslators! x) (← applyTranslators! y)
  | _           => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($x : Int) < $y) => return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Int) ≤ $y) => return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Int) ≥ $y) => return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Int) > $y) => return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  | _                   => return none

end Smt.Translate.Int
