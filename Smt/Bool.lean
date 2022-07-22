/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean
import Smt.Translator

namespace Smt.Bool

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | const `Bool.true _                             => return symbolT "true"
  | const `Bool.false _                            => return symbolT "false"
  | app (app (const `BEq.beq _) (const `Bool _)) _ => return symbolT "="
  | _                                              => return none

@[smtTranslator] def replaceEq : Translator
  | app (app (const `Decidable.decide _)
             (app (app (app (const `Eq _) (const `Bool _))
                       a) b)) _ => do
    let tmA ← applyTranslators! a
    let tmB ← applyTranslators! b
    return Term.mkApp2 (symbolT "=") tmA tmB
  | _ => return none

end Smt.Bool
