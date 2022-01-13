import Lean

/-- Returns `true` if `sub` is a substring of `s` and `false` otherwise. -/
partial def String.isSubStrOf (sub : String) (s : String) : Bool :=
  loop 0
  where
    loop i :=
    if i + sub.length > s.length then false
    else String.substrEq sub 0 s i sub.length ∨ loop (i + 1)

namespace Smt.Util

open Lean
open Lean.Expr

/-- Prints the given expression in AST format. -/
def exprToString : Expr → String
  | bvar id _        => s!"(BVAR {id})"
  | fvar id _        => s!"(FVAR {id.name})"
  | mvar id _        => s!"(MVAR {id.name})"
  | sort l _         => s!"(SORT {l})"
  | const id l _     => s!"(CONST {id} {l})"
  | app f x _        => s!"(APP {exprToString f} {exprToString x})"
  | lam id s e _     => s!"(LAM {id} {exprToString s} {exprToString e})"
  | forallE id s e _ => s!"(FORALL {id} {exprToString s} {exprToString e})"
  | letE id s v e _  =>
    s!"(LET {id} {exprToString s} {exprToString v} {exprToString e})"
  | lit l _          => s!"(LIT {literalToString l})"
  | mdata m e _      => s!"(MDATA {m} {exprToString e})"
  | proj s i e _     => s!"(PROJ {s} {i} {exprToString e})"
  where
    literalToString : Literal → String
      | Literal.natVal v => ⟨Nat.toDigits 10 v⟩
      | Literal.strVal v => v

/-- Returns all free variables in the given expression. -/
def getFVars (e : Expr) : List Expr := (getFVars' e).eraseDups
  where
    getFVars' : Expr → List Expr
      | forallE _ d b _ => getFVars' d ++ getFVars' b
      | lam _ d b _     => getFVars' d ++ getFVars' b
      | letE _ t v b _  => getFVars' t ++ getFVars' v ++ getFVars' b
      | app f a _       => getFVars' f ++ getFVars' a
      | mdata _ b _     => getFVars' b
      | proj _ _ b _    => getFVars' b
      | fvar id d       => [fvar id d]
      | _               => []

/-- Returns all meta variables in the given expression. -/
def getMVars (e : Expr) : List Expr := (getMVars' e).eraseDups
  where
    getMVars' : Expr → List Expr
      | forallE _ d b _ => getMVars' d ++ getMVars' b
      | lam _ d b _     => getMVars' d ++ getMVars' b
      | letE _ t v b _  => getMVars' t ++ getMVars' v ++ getMVars' b
      | app f a _       => getMVars' f ++ getMVars' a
      | mdata _ b _     => getMVars' b
      | proj _ _ b _    => getMVars' b
      | mvar id d       => [mvar id d]
      | _               => []

/-- Does the expression `e` contain meta variables? -/
def hasMVars (e : Expr) : Bool := !(getMVars e).isEmpty

/-- Set of constants defined by SMT-LIB. -/
def smtConsts : Std.HashSet String :=
  List.foldr (fun c s => s.insert c) Std.HashSet.empty
  [
    "=",
    "distinct",
    "Bool",
    "true",
    "false",
    "not",
    "and",
    "or",
    "exists",
    "=>",
    "Int",
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

/-- Returns all unknown constants in the given expression. -/
def getUnkownConsts : Expr → List Expr
  | app f e _       => getUnkownConsts f ++ getUnkownConsts e
  | lam _ t b _     => getUnkownConsts t ++ getUnkownConsts b
  | forallE _ t b _ => getUnkownConsts t ++ getUnkownConsts b
  | letE _ t v b _  => getUnkownConsts t ++ getUnkownConsts v ++ getUnkownConsts b
  | mdata _ e _     => getUnkownConsts e
  | proj _ _ e _    => getUnkownConsts e
  | e@(const ..)    => if smtConsts.contains (toString e) then [] else [e]
  | _               => []

namespace Smt.Util
