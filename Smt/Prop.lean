import Lean
import Smt.Transformer

namespace Smt.Prop

open Lean
open Lean.Expr
open Smt.Transformer

/-- Traverses `e` and marks arrows for replacement with `Imp`. For example,
    given `(FORALL _ p q)`, this method should mark the given expr for
    replacement with `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the pre-processing step. -/
@[Smt] partial def markImps : Transformer := fun e => markImps' #[] e
  where
    markImps' xs e := do match e with
      | app f e d           => markImps' xs f; markImps' xs e
      | lam n t b d         =>
        markImps' xs t;
        Meta.withLocalDecl n d.binderInfo t (fun x => markImps' (xs.push x) b)
      | e@(forallE n t b d) =>
        markImps' xs t
        let ti := t.instantiate xs
        if (e.instantiate xs).isArrow ∧ (← Meta.inferType ti).isProp then
          markImps' xs b
          addMark e (mkApp2 imp t (b.lowerLooseBVars 1 1))
        else
          Meta.withLocalDecl n d.binderInfo t (fun x => markImps' (xs.push x) b)
      | letE n t v b d      =>
        markImps' xs t
        markImps' xs v
        Meta.withLetDecl n t v (fun x => markImps' (xs.push x) b)
      | mdata m e s         => markImps' xs e
      | proj s i e d        => markImps' xs e
      | e                   => ()
    imp := mkConst (Name.mkSimple "=>")

end Smt.Prop
