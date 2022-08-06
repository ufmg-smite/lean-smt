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

partial def parse (s : String) : Except ParseError (List Sexp) := do
  let tks ← tokenize #[] s.toSubstring
  parseMany #[] tks.toList |>.map Prod.fst |>.map Array.toList
where
  /-- Push tokens found in `s` onto the `stk`. Supported token kinds are more or less as in
  https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf:
  - parentheses `(`/`)`
  - symbols `abc`
  - quoted symbols `|abc|`
  - string literals `"abc"` -/
  tokenize (stk : Array Substring) (s : Substring) : Except ParseError (Array Substring) :=
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
          tokenize (stk.push s1) s2
      else if c == ')' || c == '(' then
        tokenize (stk.push <| s.take 1) (s.drop 1)
      else if c.isWhitespace then
        tokenize stk (s.drop 1)
      else
        let tk := s.takeWhile fun c =>
          !c.isWhitespace && c != '(' && c != ')' && c != '|' && c != '"'
        -- assertion: tk.bsize > 0 as otherwise we would have gone into one of the branches above
        tokenize (stk.push tk) (s.extract ⟨tk.bsize⟩ ⟨s.bsize⟩)

  parseOne : List Substring → Except ParseError (Sexp × List Substring)
    | tk :: tks => do
      if tk.front == ')' then
        throw <| .malformed "mismatched parentheses"
      if tk.front == '(' then
        let (ss, tks) ← parseMany #[] tks
        return (expr ss.toList, tks)
      else
        return  (atom tk.toString, tks)
    | [] => throw <| .incomplete "expected input, got none"

  parseMany (stk : Array Sexp) : List Substring → Except ParseError (Array Sexp × List Substring)
    | tk :: tks => do
      if tk.front == ')' then .ok (stk, tks)
      else
        let (e, tks) ← parseOne (tk :: tks)
        parseMany (stk.push e) tks
    | [] => .ok (stk, [])

end Sexp
