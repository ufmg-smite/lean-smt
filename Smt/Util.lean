import Lean

namespace Smt.Util

open Lean
open Lean.Expr

/-- Prints the given expression in AST format. -/
def exprToString : Expr → String
  | bvar id _         => "(BVAR " ++ ⟨Nat.toDigits 10 id⟩ ++ ")"
  | fvar id _         => "(FVAR " ++ id.name.toString ++ ")"
  | mvar id _         => "(MVAR " ++ id.name.toString ++ ")"
  | sort l _          => "(SORT " ++ l.format.pretty ++ ")"
  | const id _ _      => "(CONST " ++ id.toString ++ ")"
  | app f x _         => "(APP " ++ exprToString f ++ " " ++ exprToString x
                                 ++ ")"
  | lam id s e _      => "(LAM " ++ id.toString ++ " " ++ exprToString s
                                 ++ " " ++ exprToString e ++ ")"
  | forallE id s e _  => "(FORALL " ++ id.toString ++ " " ++ exprToString s
                                    ++ " " ++ exprToString e ++ ")"
  | letE id s e e' _  => "(LET " ++ id.toString ++ " " ++ exprToString s
                                 ++ " " ++ exprToString e ++ " "
                                 ++ exprToString e ++ ")"
  | lit l _           => "(LIT " ++ literalToString l ++ ")"
  | mdata m e _       => "(MDATA " ++ mdataToString m ++ " " ++ exprToString e
                                   ++ ")"
  | proj s i e _      => "(PROJ" ++ s.toString ++ " " ++ ⟨Nat.toDigits 10 i⟩
                                 ++ " " ++ exprToString e ++ ")"
  where
    literalToString : Literal → String
      | Literal.natVal v => ⟨Nat.toDigits 10 v⟩
      | Literal.strVal v => v
    mdataToString : MData → String
      | _ => ""

/-- Returns all free variables in the given expression. -/
def getFVars : Expr → List Expr
  | forallE _ d b _ => getFVars d ++ getFVars b
  | lam _ d b _     => getFVars d ++ getFVars b
  | letE _ t v b _  => getFVars t ++ getFVars v ++ getFVars b
  | app f a _       => getFVars f ++ getFVars a
  | mdata _ b _     => getFVars b
  | proj _ _ b _    => getFVars b
  | fvar id d       => [fvar id d]
  | _               => []

/-- Converts the given constant into the corresponding SMT constant/function
    symbol. -/
def knownConsts : Std.HashMap String String :=
  List.foldr (fun (k, v) m => m.insert k v) Std.HashMap.empty
  [
    ("Eq" , "="),
    ("Ne", "distinct"),
    ("Prop", "Bool"),
    ("True", "true"),
    ("False", "false"),
    ("Not", "not"),
    ("And", "and"),
    ("Or" , "or"),
    ("Iff", "="),
    ("Imp", "=>"),
    ("Bool.true", "true"),
    ("Bool.false", "false"),
    ("not", "not"),
    ("and", "and"),
    ("or", "or"),
    ("BEq.beq", "="),
    ("Int", "Int"),
    ("HAdd.hAdd", "+"),
    ("HSub.hSub", "-"),
    ("HMul.hMul", "*"),
    ("HDiv.hDiv", "/"),
    ("HMod.hMod", "mod"),
    ("Nat.min", "min"),
    ("Nat.zero", "0"),
    ("GE.ge", ">="),
    ("natMinus", "natMinus")
  ]

/-- Returns all unknown constants in the given expression. -/
def getUnkownConsts : Expr → List Expr
  | app f e d       => getUnkownConsts f ++ getUnkownConsts e
  | lam n t b d     => getUnkownConsts t ++ getUnkownConsts b
  | forallE n t b d => getUnkownConsts t ++ getUnkownConsts b
  | letE n t v b d  => getUnkownConsts t ++ getUnkownConsts v ++ getUnkownConsts b
  | mdata m e s     => getUnkownConsts e
  | proj s i e d    => getUnkownConsts e
  | e@(const n l d) => if knownConsts.contains n.toString then [] else [e]
  | e               => []

namespace Smt.Util
