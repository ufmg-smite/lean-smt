/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.String

open Lean Expr
open Smt.Transformer

@[Smt] def replaceConst : Transformer
  | const `Char.ofNat ..     => pure none
  | const `String.Pos.mk ..  => pure none
  | const `String.replace .. => pure (mkConst `str.replace_all)
  | const `String.length ..  => pure (mkConst `str.len)
  | const `String.append ..  => pure (mkConst (Name.mkSimple "str.++"))
  | e                        => pure e

@[Smt] def replaceStringGetOp : Transformer
  | app (app (const `String.getOp ..) f _) e _ => do
    return match ← applyTransformations f, ← applyTransformations e with
    | some f', some e' =>
      mkApp (mkConst `str.to_code) (mkApp2 (mkConst `str.at) f' e')
    | _      , _       => none
  | e                                          => pure e

@[Smt] def replaceStringContains : Transformer
  | app (app (const `String.contains ..) f _) e _ => do
    return match ← applyTransformations f, ← applyTransformations e with
    | some f', some e' =>
      mkApp2 (mkConst `str.contains) f' (mkApp (mkConst `str.from_code) e')
    | _      , _       => none
  | e                                             => pure e

@[Smt] def replaceStringLt : Transformer
  | app (app (app (app (const `List.lt ..) ..) ..)
        (app (const `String.data ..) a _) _)
        (app (const `String.data ..) b _) _ => do
    return match ← applyTransformations a, ← applyTransformations b with
    | some a', some b' =>
      mkApp2 (mkConst (Name.mkSimple "str.<")) a' b'
    | _      , _       => none
  | e                                       => pure e

end Smt.String
