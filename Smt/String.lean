/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.String

open Lean
open Lean.Expr
open Smt.Transformer

@[Smt] def transformStringGetOp : Transformer
  | app (app (const `String.getOp ..) f _) e _ => do
    return match ← applyTransformations f, ← applyTransformations e with
    | some f', some e' =>
      mkApp (mkConst `str.to_code) (mkApp2 (mkConst `str.at) f' e')
    | _      , _       => none
  | e                                          => return e

@[Smt] def transformStringContains : Transformer
  | app (app (const `String.contains ..) f _) e _ => do
    return match ← applyTransformations f, ← applyTransformations e with
    | some f', some e' =>
      mkApp2 (mkConst `str.contains) f' (mkApp (mkConst `str.from_code) e')
    | _      , _       => none
  | e                                             => return e

end Smt.String
