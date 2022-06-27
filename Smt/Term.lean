/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt

/-- The SMT-LIBv2 Term data-structure. -/
inductive Term where
  | /-- A theory literal -/
    Literal : String → Term
  | /-- Sort or function symbol -/
    Symbol  : String → Term
  | /-- Function sort -/
    Arrow   : Term → Term → Term
  | /-- Function application -/
    App     : Term → Term → Term
  | /-- Forall quantifier -/
    Forall  : String → Term → Term → Term
  | /-- Exists quantifier -/
    Exists  : String → Term → Term → Term
  | /-- Let binding -/
    Let     : String → Term → Term → Term
  deriving Inhabited

namespace Term

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
  | Literal l    => l             -- do not quote theory literals
  | Symbol n     => quoteSymbol n
  | Arrow d c    =>
    let ss := arrowToList (Arrow d c)
    "(" ++ String.intercalate " " (ss.init.map toString) ++ ") "
        ++ ss.getLast!.toString
  | App f t      =>
    let ts := List.reverse <| appToList (App f t)
    "(" ++ String.intercalate " " (ts.map toString) ++ ")"
  | Forall n s t => s!"(forall (({quoteSymbol n} {s.toString})) {t.toString})"
  | Exists n s t => s!"(exists (({quoteSymbol n} {s.toString})) {t.toString})"
  | Let n t b => s!"(let (({quoteSymbol n} {t.toString})) {b.toString})"
  where
    arrowToList : Term → List Term
      | Arrow d c => d :: arrowToList c
      | s         => [s]
    appToList : Term → List Term
      | App f t => t :: appToList f
      | s       => [s]

instance : ToString Term where
  toString := toString

instance : Std.ToFormat Term where
  format := Std.Format.text ∘ toString

end Term
end Smt
