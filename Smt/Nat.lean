import Lean
import Smt.Transformer

namespace Smt.Nat

open Lean
open Lean.Expr
open Smt.Transformer

/-- Traverses `e` and marks type casts of literals to `Nat` for replacement with
    just the literals. For example, given
    `(app (app (app (OfNat.ofNat ..) ..) (LIT 0) ..) ..)`, this method should
    mark the whole expr for replacement with just `(LIT 0)`. -/
@[Smt] partial def markNatLiterals : Transformer := fun e => do match e with
  | a@(app f e d)   => match toLiteral f with
    | none   => markNatLiterals f; markNatLiterals e
    | some l => addMark a l
  | lam n t b d     => markNatLiterals t; markNatLiterals b
  | forallE n t b d => markNatLiterals t; markNatLiterals b
  | letE n t v b d  => markNatLiterals t; markNatLiterals v; markNatLiterals b
  | mdata m e s     => markNatLiterals e
  | proj s i e d    => markNatLiterals e
  | e               => ()
  where
    toLiteral : Expr → Option Expr
      | app (app (const n ..) ..) l .. => if n == `OfNat.ofNat then l else none
      | e                              => none

/-- Traverses `e` and marks `Nat` constructors `Nat.zero` and `Nat.succ n` for
    replacement with `0` and `(+ n 1)`. -/
@[Smt] partial def markNatCons : Transformer := fun e => do match e with
  | a@(app (const `Nat.succ ..) e d) =>
    markNatCons e
    addMark a (plusOne e)
  | app f e d                => markNatCons f; markNatCons e
  | lam n t b d              => markNatCons t; markNatCons b
  | forallE n t b d          => markNatCons t; markNatCons b
  | letE n t v b d           => markNatCons t; markNatCons v; markNatCons b
  | mdata m e s              => markNatCons e
  | proj s i e d             => markNatCons e
  | e@(const n ..)           => if n == `Nat.zero then
                                  addMark e (mkLit (Literal.natVal 0))
  | e                        => ()
  where
    plusOne e :=
      mkApp2 (mkConst (Name.mkSimple "+")) e (mkLit (Literal.natVal 1))

/-- Traverses `e` and marks quantified expressions over natural numbers for
    replacement with versions that ensure the quantified variables are greater
    than or equal to 0. For example, given `∀ x : Nat, p(x)`, this method
    should mark the expr for replacement with `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[Smt] partial def markNatForalls : Transformer := fun e => markImps' #[] e
  where
    markImps' xs e := do match e with
      | app f e d           => markImps' xs f; markImps' xs e
      | lam n t b d         =>
        markImps' xs t
        Meta.withLocalDecl n d.binderInfo t (fun x => markImps' (xs.push x) b)
      | e@(forallE n t@(const `Nat ..) b d) =>
        markImps' xs t
        if ¬(e.instantiate xs).isArrow then
          addMark e (mkForall n d.binderInfo t (imp b))
        Meta.withLocalDecl n d.binderInfo t (fun x => markImps' (xs.push x) b)
      | e@(forallE n t b d) =>
        markImps' xs t
        Meta.withLocalDecl n d.binderInfo t (fun x => markImps' (xs.push x) b)
      | letE n t v b d      =>
        markImps' xs t
        markImps' xs v
        Meta.withLetDecl n t v (fun x => markImps' (xs.push x) b)
      | mdata m e s         => markImps' xs e
      | proj s i e d        => markImps' xs e
      | e                   => ()
    imp e := mkApp2 (mkConst (Name.mkSimple "=>"))
                    (mkApp2 (mkConst (Name.mkSimple ">="))
                            (mkBVar 0)
                            (mkLit (Literal.natVal 0)))
                    e

end Smt.Nat
