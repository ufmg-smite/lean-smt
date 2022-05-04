import Lean
import Smt.Transformer

namespace Smt.Nat

open Lean
open Lean.Expr
open Smt.Transformer

/-- Removes casts of literals to `Nat` in `e`. For example, given
    `(app (app (app (OfNat.ofNat ..) ..) (LIT 0) ..) ..)`, this method removes
    all applications and returns just `(LIT 0)`. -/
@[Smt] def markNatLiterals : Transformer
  | app (app (app (const ``OfNat.ofNat ..) ..) l ..) .. => pure l
  | e                                                   => pure e

/-- Replaces `Nat` constructors `Nat.zero` and `Nat.succ n` for with `0` and
    `(+ n 1)`. -/
@[Smt] def markNatCons : Transformer
  | const ``Nat.zero ..           => pure $ mkLit (Literal.natVal 0)
  | app (const ``Nat.succ ..) e _ => do match ← applyTransformations e with
    | none    => pure $ none
    | some e' => pure $ plusOne e'
  | e                             => pure e
  where
    plusOne e :=
      mkApp2 (mkConst (Name.mkSimple "+")) e (mkLit (Literal.natVal 1))

/-- Replaces quantified expressions over natural numbers for with versions that
    ensure the quantified variables are greater than or equal to 0. For
    example, given `∀ x : Nat, p(x)`, this method returns the expr
    `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[Smt] def markNatForalls : Transformer
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
