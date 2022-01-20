import Lean
import Smt.Constants
import Smt.Transformer

namespace Smt.General

open Lean
open Lean.Expr
open Smt.Constants
open Smt.Transformer

/-- Traverses `e` and marks type arguments in apps for removal. For example,
    given `(App (App (App Eq Prop) p) q)`, this method should mark `Prop` for
    removal and the resulting expr will be `(App (App Eq p) q)`. -/
@[Smt] partial def markTypeArgs : Transformer := fun e => markTypeArgs' #[] e
  where
    markTypeArgs' xs e := do match e with
      | app a@(app (const `Exists ..) ..) e d =>
        markTypeArgs' xs a
        markTypeArgs' xs e
      | app f e d                             =>
        markTypeArgs' xs f
        if ← hasValidSort (e.instantiate xs) then markTypeArgs' xs e
        else addMark e none
      | lam n t b d                           =>
        markTypeArgs' xs t
        Meta.withLocalDecl n d.binderInfo t (λ x => markTypeArgs' (xs.push x) b)
      | forallE n t b d                       =>
        markTypeArgs' xs t
        Meta.withLocalDecl n d.binderInfo t (λ x => markTypeArgs' (xs.push x) b)
      | letE n t v b d                        =>
        markTypeArgs' xs t
        markTypeArgs' xs v
        Meta.withLetDecl n t v (λ x => markTypeArgs' (xs.push x) b)
      | mdata m e s                           => markTypeArgs' xs e
      | proj s i e d                          => markTypeArgs' xs e
      | e                                     => ()
    -- Returns the whether or not we should add `e` to the argument list
    -- (i.e., skip implicit sort arguments).
    hasValidSort (e : Expr) : MetaM Bool := do
      let type ← Meta.inferType e
      match type with
      | sort l ..  => l.isZero
      | forallE .. => false    -- All arguments must be first order.
      | _          => true

/-- Traverses `e` and marks type class instantiations in apps for removal. For
    example, given `(APP instOfNatNat (LIT 1))`, this method should mark
    `instOfNatNat` for removal and the resulting expr will be `(LIT 1)`. -/
@[Smt] partial def markInstArgs : Transformer := fun e => do match e with
  | app f e d       =>
    markInstArgs f
    if ¬isInst e then markInstArgs e else addMark e none
  | lam n t b d     => markInstArgs t; markInstArgs b
  | forallE n t b d => markInstArgs t; markInstArgs b
  | letE n t v b d  => markInstArgs t; markInstArgs v; markInstArgs b
  | mdata m e s     => markInstArgs e
  | proj s i e d    => markInstArgs e
  | e               => if isInst e then addMark e none else ()
  where
    -- Checks whether `e` is a type class instantiation.
    -- TODO: Too fragile, replace with better checks.
    isInst (e : Expr) : Bool := 
    match e with
    | const n .. => "inst".isSubStrOf n.toString
    | _          => false

@[Smt] def markOfNat : Transformer := fun e => do match e with
  | a@(app (const `Char.ofNat ..) e _)  =>
    addMark a e
    markOfNat e
  | a@(app (const `Int.ofNat ..) e _)  =>
    addMark a e
    markOfNat e
  | app f e _       => markOfNat f; markOfNat e
  | lam _ _ b _     => markOfNat b
  | mdata _ e _     => markOfNat e
  | proj _ _ e _    => markOfNat e
  | letE _ _ v b _  => markOfNat v; markOfNat b
  | forallE _ t b _ => markOfNat t; markOfNat b
  | _               => ()

/-- Traverses `e` and marks Lean constants for replacement with corresponding
    SMT-LIB versions. For example, given `"a" < "b"`, this method should mark
    `<` for replacement with `str.<`. -/
@[Smt] def markKnownConsts : Transformer := fun e => do
  match knownConsts.find? e with
  | some e' => addMark e e'
  | none   => match e with
    | app f e _       => markKnownConsts f; markKnownConsts e
    | lam _ _ b _     => markKnownConsts b
    | mdata _ e _     => markKnownConsts e
    | proj _ _ e _    => markKnownConsts e
    | letE _ _ v b _  => markKnownConsts v; markKnownConsts b
    | forallE _ t b _ => markKnownConsts t; markKnownConsts b
    | _               => ()

end Smt.General
