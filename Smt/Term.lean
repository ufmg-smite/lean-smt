/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Data.Sexp
import Smt.Dsl.Sexp

namespace Smt

/-- The SMT-LIBv2 Term data-structure.

Ctors are postfixed with T to disambiguate from keywords and `Expr`. -/
inductive Term where
  | /-- A theory literal -/
    literalT : String → Term
  | /-- Sort or function symbol -/
    symbolT  : String → Term
  | /-- Function sort -/
    arrowT   : Term → Term → Term
  | /-- Function application -/
    appT     : Term → Term → Term
  | /-- Forall quantifier -/
    forallT  : String → Term → Term → Term
  | /-- Exists quantifier -/
    existsT  : String → Term → Term → Term
  | /-- Let binding -/
    letT     : String → Term → Term → Term
  deriving Inhabited

namespace Term
namespace Notation

scoped infixl:20 " • "  => appT
scoped prefix:21 " ` "  => symbolT
scoped prefix:21 " `` " => literalT

end Notation

open scoped Notation

def mkApp2 (f a b : Term) : Term :=
  f • a • b

def mkApp3 (f a b c : Term) : Term :=
  f • a • b • c

def mkApp4 (f a b c d : Term) : Term :=
  f • a • b • c • d

/-- SMT-LIBv2 quoting for symbols. -/
def quoteSymbol (s : String) : String :=
  -- This is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  -- symbols.
  let valid := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~!@$%^&*_-+=<>.?/"
  if s.isEmpty then "||"
  else if s.any (fun c => ¬valid.contains c) ∨ (s.get 0 ≥ '0' ∧ s.get 0 ≤ '9') then
    -- Must quote the symbol, but it cannot contain | or \, we turn those into
    -- _.
    let s := s.map (fun c => if String.contains "\\|" c then '_' else c)
    s!"|{s}|"
  else s

/-- Print given `Term` in SMT-LIBv2 format. -/
protected partial def toSexp : Term → Sexp
  | literalT l    => sexp!{{l}}             -- do not quote theory literals
  | symbolT n     => sexp!{{quoteSymbol n}}
  | t@(arrowT ..) => sexp!{(...{List.intersperse sexp!{->} ((arrowToList t).map Term.toSexp)})}
  | t@(appT ..)   => sexp!{(...{(appToList [] t).map Term.toSexp})}
  | forallT n s t => sexp!{(forall (({quoteSymbol n} {s.toSexp})) {t.toSexp})}
  | existsT n s t => sexp!{(exists (({quoteSymbol n} {s.toSexp})) {t.toSexp})}
  | letT n t b    => sexp!{(let (({quoteSymbol n} {t.toSexp})) {b.toSexp})}
where
  arrowToList : Term → List Term
    | arrowT d c => d :: arrowToList c
    | s          => [s]
  appToList (acc : List Term) : Term → List Term
    -- We hardcode support for the `(_ extract i j)` term which needs to be parenthesized
    -- since SMT-LIB does not curry applications. `(_ BitVec n)` does not need special
    -- casing since it is not a function, so it should not be the head of an `appT`.
    | appT (symbolT "_") (symbolT "extract") =>
      let i := acc.get! 0
      let j := acc.get! 1
      literalT (toString sexp!{(_ extract {i.toSexp} {j.toSexp})}) :: acc.drop 2
    -- Support the non-standard constant array constructor.
    | appT (symbolT "as") (symbolT "const") =>
      let t := acc.get! 0
      literalT s!"(as const {Term.toSexp t})" :: acc.drop 1
    | appT f t => appToList (t :: acc) f
    | s        => s :: acc

instance : ToSexp Term := ⟨Term.toSexp⟩

instance : ToString Term := ⟨toString ∘ ToSexp.toSexp⟩

instance : Std.ToFormat Term where
  format := Std.Format.text ∘ toString

end Term
end Smt
