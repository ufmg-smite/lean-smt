/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.Nat

open Lean Expr
open Smt.Transformer

@[Smt] def replaceConst : Transformer
  | const `Nat.add ..  => pure (mkConst (Name.mkSimple "+"))
  | const `Nat.le ..   => pure (mkConst (Name.mkSimple "<="))
  | app (app (const `GE.ge ..) (const `Nat ..) _) .. =>
    pure (mkConst (Name.mkSimple ">="))
  | e                  => pure e

/-- Removes casts of literals to `Nat` in `e`. For example, given
    `(app (app (app (OfNat.ofNat ..) ..) (LIT 0) ..) ..)`, this method removes
    all applications and returns just `(LIT 0)`. -/
@[Smt] def removeOfNat : Transformer
  | app (app (app (const ``OfNat.ofNat ..) ..) l ..) .. => pure l
  | e                                                   => pure e

/-- Replaces `Nat` constructors `Nat.zero` and `Nat.succ n` for with `0` and
    `(+ n 1)`. -/
@[Smt] def replaceCtr : Transformer
  | const ``Nat.zero ..           => pure $ mkLit (Literal.natVal 0)
  | app (const ``Nat.succ ..) e _ => do match ← applyTransformations e with
    | none    => pure none
    | some e' => pure $ plusOne e'
  | e                             => pure e
  where
    plusOne e :=
      mkApp2 (mkConst (Name.mkSimple "+")) e (mkLit (Literal.natVal 1))

/-- Removes applications of `Nat.decLe` in `e`.
    TODO: replace by unfolding projections. -/
@[Smt] def removeDecLe : Transformer
  | app (app f (app (app (const ``Nat.decLe ..) ..) ..) ..) e .. => do
    return match ← applyTransformations f, ← applyTransformations e with
    | none  , none   => none
    | none  , some e => e
    | some f, none   => f
    | some f, some e => mkApp f e
  | e                                                            =>
    pure e

/-- Replaces quantified expressions over natural numbers for with versions that
    ensure the quantified variables are greater than or equal to 0. For
    example, given `∀ x : Nat, p(x)`, this method returns the expr
    `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[Smt] def replaceForalls : Transformer
  | e@(forallE n t@(const ``Nat ..) b d) => do
    -- TODO: replace check with final domain and improve returned result.
    if ¬e.isArrow then
      match ← applyTransformations t,
            ← Meta.withLocalDecl n d.binderInfo t (applyTransformations' b) with
      | some t', some b' => pure $ mkForall n d.binderInfo t' (imp b')
      | _      , _       => pure e
    else return e
  | e                                   => pure e
  where
    applyTransformations' b x := do
      let mut b' ← applyTransformations (b.instantiate #[x])
      if let some b'' := b' then
        b' := some (b''.abstract #[x])
      return b'
    imp e := mkApp2 (mkConst (Name.mkSimple "=>"))
                    (mkApp2 (mkConst (Name.mkSimple ">="))
                            (mkBVar 0)
                            (mkLit (Literal.natVal 0)))
                    e

end Smt.Nat
