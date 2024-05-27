/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Batteries.Classes.Cast
import Batteries.Data.Int.Lemmas
import Smt.Translator

namespace Smt.Int

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | const ``Int.add _  => return symbolT "+"
  | const ``Int.sub _  => return symbolT "-"
  | const ``Int.neg _  => return symbolT "-"
  | const ``Int.mul _  => return symbolT "*"
  | const ``Int.div _  -- TODO: one of these is probably wrong
  | const ``Int.ediv _ => return symbolT "div"
  | const ``Int.mod _  -- TODO: one of these is probably wrong
  | const ``Int.emod _ => return symbolT "mod"
  | const ``Int.le _   => return symbolT "<="
  | const ``Int.lt _   => return symbolT "<"
  | const ``Int.pow _  => return symbolT "^"
  | app (app (const ``GE.ge _) (const ``Int _)) _ => return symbolT ">="
  | app (app (const ``GT.gt _) (const ``Int _)) _ => return symbolT ">"
  | app (const ``Int.ofNat _) e => applyTranslators! e
  | app (app (app (const ``Nat.cast _) (const ``Int _)) _) e => applyTranslators! e
  | _                          => return none

end Smt.Int
