/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

/-- The type of S-expressions. -/
inductive Sexp where
  | atom : String → Sexp
  | expr : List Sexp → Sexp
  deriving Repr, BEq, Inhabited

class ToSexp (α : Type u) where
  toSexp : α → Sexp

namespace Sexp

partial def serialize : Sexp → String
  | atom s  => s
  | expr ss => "(" ++ (" ".intercalate <| ss.map serialize) ++ ")"

def serializeMany (ss : List Sexp) : String :=
  ss.map serialize |> "\n".intercalate

instance : ToString Sexp :=
  ⟨serialize⟩

inductive ParseError where
  | /-- Incomplete input, for example missing a closing parenthesis. -/
    incomplete (msg : String)
  | /-- Malformed input, for example having too many closing parentheses. -/
    malformed (msg : String)

instance : ToString ParseError where
  toString
    | .incomplete msg => s!"incomplete input: {msg}"
    | .malformed msg  => s!"malformed input: {msg}"

/-- Tokenize `s` with the s-expression grammar. Supported token kinds are more or less as in
https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf:
- parentheses `(`/`)`
- symbols `abc`
- quoted symbols `|abc|`
- string literals `"abc"` -/
partial def tokenize (s : Substring) : Except ParseError (Array Substring) :=
  go #[] s
where go (stk : Array Substring) (s : Substring) :=
  -- Note: not written using `do` notation to ensure tail-call recursion
  if s.isEmpty then .ok stk
  else
    let c := s.front
    if c == '"' || c == '|' then
      let s1 := s.drop 1 |>.takeWhile (· ≠ c)
      if s1.stopPos = s.stopPos then
        throw <| .incomplete s!"ending {c} missing after {s1}"
      else
        let s1 := ⟨s.str, s.startPos, s.next s1.stopPos⟩
        let s2 := ⟨s.str, s1.stopPos, s.stopPos⟩
        go (stk.push s1) s2
    else if c == ')' || c == '(' then
      go (stk.push <| s.take 1) (s.drop 1)
    else if c.isWhitespace then
      go stk (s.drop 1)
    else
      let tk := s.takeWhile fun c =>
        !c.isWhitespace && c != '(' && c != ')' && c != '|' && c != '"'
      -- assertion: tk.bsize > 0 as otherwise we would have gone into one of the branches above
      go (stk.push tk) (s.extract ⟨tk.bsize⟩ ⟨s.bsize⟩)

mutual
partial def parseOneAux : List Substring → Except ParseError (Sexp × List Substring)
  | tk :: tks => do
    if tk.front == ')' then
      throw <| .malformed "unexpected ')'"
    if tk.front == '(' then
      if let (ss, _tk :: tks) ← parseManyAux tks then
        -- assertion: _tk == ')' since parseManyAux only stops on ')'
        return (expr ss.toList, tks)
      else
        throw <| .incomplete "expected ')'"
    else
      return (atom tk.toString, tks)
  | [] => throw <| .incomplete "expected a token, got none"

partial def parseManyAux :=
  go #[]
where go (stk : Array Sexp) : List Substring → Except ParseError (Array Sexp × List Substring)
  | tk :: tks => do
    if tk.front == ')' then .ok (stk, tk :: tks)
    else
      let (e, tks) ← parseOneAux (tk :: tks)
      go (stk.push e) tks
  | [] => .ok (stk, [])
end

/-- Parse all the s-expressions in the given string. For example, `"(abc) (def)"` contains two. -/
def parseMany (s : String) : Except ParseError (List Sexp) := do
  let tks ← tokenize s.toSubstring
  let (sexps, tks) ← parseManyAux tks.toList
  if !tks.isEmpty then
    throw <| .malformed s!"unexpected '{tks.get! 0}'"
  return sexps.toList

/-- Parse a single s-expression. Note that the string may contain extra data, but parsing will
succeed as soon as the single s-exp is complete. -/
def parseOne (s : String) : Except ParseError Sexp := do
  let tks ← tokenize s.toSubstring
  let (sexp, _) ← parseOneAux tks.toList
  return sexp

end Sexp
