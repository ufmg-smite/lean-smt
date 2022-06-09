/-- The type of S-expressions. -/
inductive Sexp where
  | atom : String → Sexp
  | expr : List Sexp → Sexp
  deriving Repr, BEq, Inhabited

namespace Sexp

partial def serialize : Sexp → String
  | atom s  => s
  | expr ss => "(" ++ (" ".intercalate <| ss.map serialize) ++ ")"

def serializeMany (ss : List Sexp) : String :=
  ss.map serialize |> "\n".intercalate

instance : ToString Sexp :=
  ⟨serialize⟩

partial def parse (s : String) : Except String (List Sexp) :=
  let tks := tokenize #[] s.toSubstring
  parseMany #[] tks.toList |>.map Prod.fst |>.map Array.toList
where
  tokenize (stk : Array Substring) (s : Substring) : Array Substring :=
    if s.isEmpty then stk
    else
      let c := s.front
      if c == ')' || c == '(' then
        tokenize (stk.push <| s.take 1) (s.drop 1)
      else if c.isWhitespace then tokenize stk (s.drop 1)
      else
        let tk := s.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')'
        if tk.bsize > 0 then tokenize (stk.push tk) (s.extract ⟨tk.bsize⟩ ⟨s.bsize⟩)
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