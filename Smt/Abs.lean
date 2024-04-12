/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Translator
import Mathlib.Algebra.Order.Group.Abs

namespace Smt.Abs

open Lean Expr
open Translator Term


@[smtTranslator] def replaceAbs : Translator
  | app (app (app (app (const ``abs _) _) _) _) e => do
      let tmE ← applyTranslators! e
      return appT (symbolT "abs") tmE
  | _ => return none

end Smt.Abs
