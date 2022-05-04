import Lean
import Smt.Transformer

namespace Smt.Prop

open Lean
open Lean.Expr
open Smt.Transformer

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
