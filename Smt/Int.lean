/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.Int

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | app (const `Int.ofNat _) e => applyTranslators! e
  | const `Int.add _           => return symbolT "+"
  | const `Int.sub _           => return symbolT "-"
  | const `Int.neg _           => return symbolT "-"
  | const `Int.mul _           => return symbolT "*"
  | const `Int.div _           => return symbolT "div"
  | const `Int.mod _           => return symbolT "mod"
  | const `Int.le _            => return symbolT "<="
  | const `Int.lt _            => return symbolT "<"
  | _                          => return none

end Smt.Int
