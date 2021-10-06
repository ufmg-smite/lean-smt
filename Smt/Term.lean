namespace Smt

/-- The Term data-structure. -/
inductive Term where
  | Const : String → Term                -- Sorts and function symbols
  | Var : String → Term                  -- Bound variables
  | Arrow : List Term → Term             -- Function sorts
  | App : String → List Term → Term      -- Function application
  | Forall : String → Term → Term → Term -- Forall quantifier
  deriving Inhabited

namespace Term
/-- SMT-LIB 2 quoting for symbols. -/
def quote (s : String) : String :=
  -- This is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  -- symbols.
  let valid := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~!@$%^&*_-+=<>.?/"
  if s.any (fun c => ¬valid.contains c) ∨ s.isEmpty ∨ (s[0] ≥ '0' ∧ s[0] ≤ '9') then
    -- Must quote the symbol, but it cannot contain | or \, we turn those into _.
    let s := s.map (fun c => if String.contains "\\|" c then '_' else c)
    "|" ++ s ++ "|"
  else s

/-- Print given `Term` in SMT-LIBv2 format. -/
partial def toString : Term → String
  | Const id => quote id
  | Var id => quote id
  | Arrow ts => "(" ++ String.intercalate " " (ts.map toString) ++ ")"
  | App f ts => "(" ++ quote f ++ " " ++ String.intercalate " " (ts.map toString) ++ ")"
  | Forall n s t => "(forall ((" ++ quote n ++ " " ++ s.toString ++ ")) " ++ t.toString ++ ")"

end Term
end Smt
