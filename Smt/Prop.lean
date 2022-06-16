/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.Prop

open Lean Expr
open Smt.Transformer

@[Smt] def replaceConst : Transformer
  | sort (.zero _) _          => pure (mkConst `Bool)
  | const `True ..            => pure (mkConst `true)
  | const `False ..           => pure (mkConst `false)
  | const `Not ..             => pure (mkConst `not)
  | const `And ..             => pure (mkConst `and)
  | const `Or ..              => pure (mkConst `or)
  | const `Iff ..             => pure (mkConst (Name.mkSimple "="))
  | app (const `Eq ..) ..     => pure (mkConst (Name.mkSimple "="))
  | app (const `Ne ..) ..     => pure (mkConst `distinct)
  | app (const `Exists ..) .. => pure (mkConst `exists)
  | app (const `ite ..) ..    => pure (mkConst `ite)
  | e                         => pure e

/-- Replaces arrows with `Imp`. For example, given `(FORALL _ p q)`, this
    method returns `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the transform step. -/
@[Smt] partial def transformImps : Transformer
  | e@(forallE n t b d) => do
    -- TODO: replace the first check with proper final domain check
    return if e.isArrow ∧ (← Meta.inferType t).isProp then
      match ← applyTransformations t,
            ← Meta.withLocalDecl n d.binderInfo t
                (fun x => applyTransformations (b.instantiate #[x])) with
      | some t', some b' => mkApp2 imp t' b'
      | _      , _       => e
    else e
  | e                   => return e
  where
    imp := mkConst (Name.mkSimple "=>")

end Smt.Prop
