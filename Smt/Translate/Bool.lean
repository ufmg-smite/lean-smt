/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Qq

import Smt.Translate

namespace Smt.Translate.Bool

open Qq
open Translator Term

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(Bool) => return symbolT "Bool"
  | _        => return none

@[smt_translate] def translateBool : Translator := fun (e : Q(Bool)) => match e with
  | ~q(true)              => return symbolT "true"
  | ~q(false)             => return symbolT "false"
  | ~q(($x : Bool) == $y) => return mkApp2 (symbolT "=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Bool) != $y) => return mkApp2 (symbolT "distinct") (← applyTranslators! x) (← applyTranslators! y)
  | _                     => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($n : Bool) = $m) => return mkApp2 (symbolT "=") (← applyTranslators! n) (← applyTranslators! m)
  | _                    => return none

end Smt.Translate.Bool
