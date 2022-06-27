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
open Smt.Translator

@[smtTranslator] def replaceConst : Translator
  | const `Bool.true ..                                 => return Term.Symbol "true"
  | const `Bool.false ..                                => return Term.Symbol "false"
  | app (app (const `BEq.beq ..) (const `Bool ..) _) .. => return Term.Symbol "="
  | _                                                   => return none

@[smtTranslator] def replaceEq : Translator
  | app (app (const `Decidable.decide ..)
             (app (app (app (const `Eq ..) (const `Bool ..) _)
                       a _) b _) ..) .. => do
    let tmA ← applyTranslators! a
    let tmB ← applyTranslators! b
    return Term.mkApp2 (Term.Symbol "=") tmA tmB
  | _                                   => return none

end Smt.Bool
