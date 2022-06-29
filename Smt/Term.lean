/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

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
  if s.any (fun c => ¬valid.contains c) ∨ s.isEmpty ∨ (s[0] ≥ '0' ∧ s[0] ≤ '9') then
    -- Must quote the symbol, but it cannot contain | or \, we turn those into
    -- _.
    let s := s.map (fun c => if String.contains "\\|" c then '_' else c)
    s!"|{s}|"
  else s

/-- Print given `Term` in SMT-LIBv2 format. -/
partial def toString : Term → String
  | literalT l    => l             -- do not quote theory literals
  | symbolT n     => quoteSymbol n
  | t@(arrowT ..) =>
    let ss := arrowToList t
    "(" ++ String.intercalate " " (ss.init.map toString) ++ ") "
        ++ ss.getLast!.toString
  | t@(appT ..) =>
    let ts := List.reverse <| appToList t
    "(" ++ String.intercalate " " (ts.map toString) ++ ")"
  | forallT n s t => s!"(forall (({quoteSymbol n} {s.toString})) {t.toString})"
  | existsT n s t => s!"(exists (({quoteSymbol n} {s.toString})) {t.toString})"
  | letT n t b    => s!"(let (({quoteSymbol n} {t.toString})) {b.toString})"
  where
    arrowToList : Term → List Term
      | arrowT d c => d :: arrowToList c
      | s          => [s]
    appToList : Term → List Term
      | appT f t => t :: appToList f
      | s        => [s]

instance : ToString Term where
  toString := toString

instance : Std.ToFormat Term where
  format := Std.Format.text ∘ toString

end Term
end Smt
