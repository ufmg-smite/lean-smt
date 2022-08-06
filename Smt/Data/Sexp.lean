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

partial def parse (s : String) : Except String (List Sexp) := do
  let tks ← tokenize #[] s.toSubstring
  parseMany #[] tks.toList |>.map Prod.fst |>.map Array.toList
where
  tokenize (stk : Array Substring) (s : Substring) : Except String (Array Substring) := do
    if s.isEmpty then
      return stk
    let c := s.front
    if c == '"' then
      let s1 := s.drop 1 |>.takeWhile (· ≠ '"')
      if s1.stopPos = s.stopPos then
        throw "ending \" missing"
      let s1 := ⟨s.str, s.startPos, s.next s1.stopPos⟩
      let s2 := ⟨s.str, s1.stopPos, s.stopPos⟩
      return (← tokenize (stk.push s1) s2)
    if c == ')' || c == '(' then
      return (← tokenize (stk.push <| s.take 1) (s.drop 1))
    if c.isWhitespace then
      return (← tokenize stk (s.drop 1))
    let tk := s.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')'
    if tk.bsize > 0 then
      return (← tokenize (stk.push tk) (s.extract ⟨tk.bsize⟩ ⟨s.bsize⟩))
    else unreachable!

  parseOne : List Substring → Except String (Sexp × List Substring)
    | tk :: tks => do
      if tk.front == ')' then
        throw "mismatched parentheses"
      if tk.front == '(' then
        let (ss, tks) ← parseMany #[] tks
        return (expr ss.toList, tks)
      else
        return  (atom tk.toString, tks)
    | [] => throw "expected input, got none"

  parseMany (stk : Array Sexp) : List Substring → Except String (Array Sexp × List Substring)
    | tk :: tks => do
      if tk.front == ')' then .ok (stk, tks)
      else
        let (e, tks) ← parseOne (tk :: tks)
        parseMany (stk.push e) tks
    | [] => .ok (stk, [])

end Sexp
