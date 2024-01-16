/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Std

import Smt.Translate.Translator

namespace Smt.Translate.Int

open Lean Expr
open Translator Term

-- TODO: preprocess `Int.div` and `Int.mod`
@[smtTranslator] def replaceConst : Translator
  | const ``Int.add _  => return symbolT "+"
  | const ``Int.sub _  => return symbolT "-"
  | const ``Int.neg _  => return symbolT "-"
  | const ``Int.mul _  => return symbolT "*"
  | const ``Int.ediv _ => return symbolT "div"
  | const ``Int.emod _ => return symbolT "mod"
  | const ``Int.le _   => return symbolT "<="
  | const ``Int.lt _   => return symbolT "<"
  | app (const ``Int.ofNat _) e => applyTranslators! e
  | app (app (app (const ``Nat.cast _) (const ``Int _)) _) e => applyTranslators! e
  | _                          => return none

end Smt.Translate.Int
