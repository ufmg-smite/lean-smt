/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.Bool

open Lean Expr
open Smt.Transformer

@[Smt] def replaceConst : Transformer
  | const `Bool.true ..                                 => pure (mkConst `true)
  | const `Bool.false ..                                => pure (mkConst `false)
  | app (app (const `BEq.beq ..) (const `Bool ..) _) .. =>
    pure (mkConst (Name.mkSimple "="))
  | e                                                   => pure e

@[Smt] def replaceEq : Transformer
  | app (app (const `Decidable.decide ..)
             (app (app (app (const `Eq ..) (const `Bool ..) _)
                       a _) b _) ..) .. =>
    return match ← applyTransformations a, ← applyTransformations b with
    | some a', some b' =>
      mkApp2 (mkConst (Name.mkSimple "=")) a' b'
    | _      , _       => none
  | e                                   => pure e

end Smt.Bool
