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
  | app (const `Int.ofNat ..) e .. => applyTranslators! e
  | const `Int.add ..              => return symbolT "+"
  | const `Int.sub ..              => return symbolT "-"
  | const `Int.neg ..              => return symbolT "-"
  | const `Int.mul ..              => return symbolT "*"
  | const `Int.div ..              => return symbolT "div"
  | const `Int.mod ..              => return symbolT "mod"
  | const `Int.le ..               => return symbolT "<="
  | const `Int.lt ..               => return symbolT "<"
  | _                              => return none

end Smt.Int
