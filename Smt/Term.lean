/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt

/-- The Term data-structure. -/
inductive Term where
  | Literal : String → Term               -- A theory literal
  | Symbol  : String → Term               -- Sorts and function symbols
  | Arrow   : Term → Term → Term          -- Function sorts
  | App     : Term → Term → Term          -- Function application
  | Forall  : String → Term → Term → Term -- Forall quantifier
  | Exists  : String → Term → Term → Term -- Exists quantifier
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
