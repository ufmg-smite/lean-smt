import Lean
import Smt.Constants
import Smt.Transformer

namespace Smt.General

open Lean
open Lean.Expr
open Smt.Constants
open Smt.Transformer

/-- Removes type arguments in the input expr. For example, given
    `(App (App (App Eq Prop) p) q)`, this method removes `Prop` and the
    resulting expr will be `(App (App Eq p) q)`. -/
@[Smt] def removeTypeArgs : Transformer
  | e@(app (app (const `Exists ..) ..) ..) => return e
  | e@(app f e' _)                         => do
    if knownConsts.contains e ∨ (← hasValidSort e') then return e
    else applyTransformations f
  | e => return e
  where
    -- Returns whether or not we should add `e` to the argument list
    -- (i.e., skip implicit sort arguments).
    hasValidSort (e : Expr) : MetaM Bool := do
      let type ← Meta.inferType e
      return match type with
      | sort l ..  => l.isZero
      | forallE .. => false    -- All arguments must be first order.
      | _          => true

/-- Removes type class instantiations from the input expr in apps. For example,
    given `(APP instOfNatNat (LIT 1))`, this method removes `instOfNatNat` and
    the resulting expr will be `(LIT 1)`. -/
@[Smt] def removeInstArgs : Transformer
  -- Checks whether `e` is a type class instantiation.
  -- TODO: Too fragile, replace with better checks.
  | e@(const n ..) => return if "inst".isSubStrOf n.toString then none else e
  | e              => return e

/-- Removes type coersion functions that convert `Nat` to `Int` and `Char`. For
    example, given `(APP instOfNatNat (LIT 1))`, this method removes
    `instOfNatNat` and the resulting expr will be `(LIT 1)`. -/
@[Smt] def removeOfNat : Transformer
  | (app (const `Char.ofNat ..) e _) => applyTransformations e
  | (app (const `Int.ofNat ..) e _)  => applyTransformations e
  | e => return e

/-- Replaces input Lean constants with with corresponding SMT-LIB versions.
    For example, given `"a" < "b"`, this method replaces `<` with `str.<`. -/
@[Smt] def replaceKnownConsts : Transformer := fun e => do
  return match knownConsts.find? e with
  | some e' => e'
  | none    => e

end Smt.General
