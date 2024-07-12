/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

/-- Returns `true` if `sub` is a substring of `s` and `false` otherwise. -/
partial def String.isSubStrOf (sub : String) (s : String) : Bool :=
  loop 0
  where
    loop i :=
    if i + sub.length > s.length then false
    else String.substrEq sub 0 s ⟨i⟩ sub.length ∨ loop (i + 1)

namespace Smt.Util

open Lean
open Lean.Expr
open Elab.Tactic

/-- Prints the given expression in AST format. -/
def exprToString : Expr → String
  | bvar id          => s!"(BVAR {id})"
  | fvar id          => s!"(FVAR {id.name})"
  | mvar id          => s!"(MVAR {id.name})"
  | sort l           => s!"(SORT {l})"
  | const id l       => s!"(CONST {id} {l})"
  | app f x          => s!"(APP {exprToString f} {exprToString x})"
  | lam id s e _     => s!"(LAM {id} {exprToString s} {exprToString e})"
  | forallE id s e _ => s!"(FORALL {id} {exprToString s} {exprToString e})"
  | letE id s v e _  => s!"(LET {id} {exprToString s} {exprToString v} {exprToString e})"
  | lit l            => s!"(LIT {literalToString l})"
  | mdata m e        => s!"(MDATA {m} {exprToString e})"
  | proj s i e       => s!"(PROJ {s} {i} {exprToString e})"
  where
    literalToString : Literal → String
      | Literal.natVal v => toString v
      | Literal.strVal v => v

/-- Count the number of occurances of the constant `c` in `e`. -/
def countConst (e : Expr) (c : Name) : Nat :=
  let rec visit : Expr → Nat
    | Expr.forallE _ d b _  => visit d + visit b
    | Expr.lam _ d b _      => visit d + visit b
    | Expr.mdata _ e        => visit e
    | Expr.letE _ t v b _   => visit t + visit v + visit b
    | Expr.app f a          => visit f + visit a
    | Expr.proj _ _ e       => visit e
    | Expr.const c' _       => if c' == c then 1 else 0
    | _                     => 0
  visit e

/-- Set of constants defined by SMT-LIB. -/
def smtConsts : HashSet String :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [
    "=",
    "distinct",
    "Bool",
    "true",
    "false",
    "not",
    "and",
    "or",
    "=>",
    "ite",
    "forall",
    "exists",
    "Int",
    "Real",
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    ">",
    "<",
    ">=",
    "<=",
    "str.<",
    "str.++",
    "str.len",
    "str.replace_all",
    "str.at",
    "str.contains",
    "str.to_code",
    "str.from_code"
  ]

/-- Like `unfoldProjInst?`, but iterated in case a typeclass projection
is defined in terms of another. -/
partial def unfoldProjInsts? (e : Expr) : MetaM (Option Expr) := do
  let some e' ← Meta.unfoldProjInst? e | return none
  let some e'' ← unfoldProjInsts? e' | return e'
  return e''

/-- Returns an expression equivalent to `e` with all typeclass projections
    unfolded. -/
def unfoldAllProjInsts : Expr → MetaM Expr :=
  Meta.transform (pre := pre)
where
  pre e : MetaM TransformStep := return match ← Meta.unfoldProjInst? e with
    | some e => .visit e
    | none   => .continue

end Smt.Util
