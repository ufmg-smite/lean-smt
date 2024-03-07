/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Qq

import Smt.Translate

namespace Smt.Translate.String

open Qq
open Lean Expr
open Translator Term

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(String) => return symbolT "String"
  | _          => return none

@[smt_translate] def translateInt : Translator := fun (e : Q(Int)) => match e with
  | ~q(String.length $x) => return appT (symbolT "str.len") (← applyTranslators! x)
  | _                    => return none

@[smt_translate] def translateString : Translator := fun (e : Q(String)) => match e with
  | ~q(.replace $z $x $y) => return mkApp3 (symbolT "str.replace_all") (← applyTranslators! z)
                                           (← applyTranslators! x) (← applyTranslators! y)
  | .lit (.strVal s) => return literalT s!"\"{s}\""
  | ~q($x ++ $y)     => return mkApp2 (symbolT "str.++") (← applyTranslators! x) (← applyTranslators! y)
  | _                => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($x : String) < $y) => return mkApp2 (symbolT "str.<") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : String) > $y) => return mkApp2 (symbolT "str.>") (← applyTranslators! x) (← applyTranslators! y)
  | _                      => return none

end Smt.Translate.String
