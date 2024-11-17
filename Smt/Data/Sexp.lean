/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Abdalrhman Mohamed, Henrik Böving
-/

import Std.Internal.Parsec.String

/-- The type of S-expressions. -/
inductive Sexp where
  | atom : String → Sexp
  | expr : List Sexp → Sexp
deriving Repr, BEq, Inhabited

class ToSexp (α : Type u) where
  toSexp : α → Sexp

namespace Sexp

def isAtom : Sexp → Bool
  | atom _ => true
  | _      => false

def isExpr : Sexp → Bool
  | expr _ => true
  | _      => false

partial def serialize : Sexp → String
  | atom s  => s
  | expr ss => "(" ++ (" ".intercalate <| ss.map serialize) ++ ")"

def serializeMany (ss : List Sexp) : String :=
  ss.map serialize |> "\n".intercalate

instance : ToString Sexp :=
  ⟨serialize⟩

namespace Parser

open Std.Internal.Parsec String

/-- Parse the s-expression grammar. Supported token kinds are more or less as in
https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf:
- parentheses `(`/`)`
- symbols `abc`
- quoted symbols `|abc|`
- string literals `"abc"`
- comments `; abc`
-/

def comment : Parser Unit := do
  skipChar ';'
  discard <| many (satisfy (· != '\n'))
  skipChar '\n' <|> eof

def misc : Parser Unit := do
  ws
  discard <| many (comment *> ws)

def strLit : Parser String := do
  let cstart ← pchar '"'
  let s ← manyCharsCore (satisfy (· ≠ '"')) cstart.toString
  let cend ← pchar '"'
  return s.push cend

def quotedSym : Parser String := do
  let cstart ← pchar '|'
  let s ← manyCharsCore (satisfy (· ≠ '|')) cstart.toString
  let cend ← pchar '|'
  return s.push cend

def sym : Parser String :=
  let filter c := !c.isWhitespace && c != '(' && c != ')' && c != '|' && c != '"' && c != ';'
  many1Chars (satisfy filter)

def atom : Parser Sexp := do
  let a ← strLit <|> quotedSym <|> sym
  return Sexp.atom a

/--
Parse all the s-expressions in the given string. For example, `"(abc) (def)"`
contains two. Note that the string may contain extra data, but parsing will
always succeed.
-/
def manySexps : Parser (List Sexp) := do
  let mut stack : List (List Sexp) := []
  let mut curr := []
  let mut next ← misc *> peek?
  while h : next.isSome do
    match next.get h with
    | '(' =>
      skipChar '('
      stack := curr :: stack
      curr := []
    | ')' =>
      match stack with
      | [] =>
        return curr.reverse
      | sexp :: sexps =>
        skipChar ')'
        stack := sexps
        curr := .expr curr.reverse :: sexp
    | _ =>
      curr := (← atom) :: curr
    next ← misc *> peek?
  if !stack.isEmpty then
    fail "expected ')'"
  return curr.reverse

def expr : Parser Sexp := do
  skipChar '('
  let sexps ← manySexps
  skipChar ')'
  return Sexp.expr sexps

/--
Parse a single s-expression. Note that the string may contain extra data, but
parsing will succeed as soon as a single s-expr is complete.
-/
def sexp : Parser Sexp :=
  atom <|> expr

/--
Parse all the s-expressions in the given string. For example, `"(abc) (def)"`
contains two. Parsing fails if there is any extra data after the last s-expr.
-/
def manySexps! : Parser (List Sexp) := do
  let sexps ← manySexps
  eof
  return sexps

/--
Parse a single s-expression. Parsing fails if there is any extra data after the
s-expr.
-/
def sexp! : Parser Sexp := do
  let s ← sexp
  eof
  return s

end Sexp.Parser
