/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Parser

import Smt.Data.Sexp

section
open Lean.Parser
open Lean.PrettyPrinter

/-- Like `ident` but with no splitting on dots and accepts anything that's not whitespace
or parentheses. So e.g. `<=` works. -/
def generalIdent : Parser :=
  withAntiquot (mkAntiquot "generalIdent" `generalIdent) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (fun c => !("(){}[].".contains c) ∧ !c.isWhitespace) "expected generalized identifier" c s
      mkNodeToken `generalIdent startPos c s }

def Lean.TSyntax.getGeneralId : TSyntax `generalIdent → String
  | ⟨.node _ `generalIdent args⟩ => args[0]!.getAtomVal!
  | _ => unreachable!

@[combinatorFormatter generalIdent] def generalIdent.formatter : Formatter := pure ()
@[combinatorParenthesizer generalIdent] def generalIdent.parenthesizer : Parenthesizer := pure ()
end

instance : Coe String Sexp :=
  ⟨Sexp.atom⟩

declare_syntax_cat sexp

syntax generalIdent : sexp
syntax "(" sexp* ")" : sexp
syntax "(" sexp* "...{" term "}" sexp* ")" : sexp
syntax "{" term "}" : sexp

-- This coercion is justified by the macro expansions below.
instance : Coe (Lean.TSyntax `sexp) (Lean.TSyntax `term) where
  coe a := ⟨a.raw⟩

macro_rules
  | `(sexp| $a:generalIdent) => `(Sexp.atom $(Lean.quote a.getGeneralId))
  | `(sexp| ( $ss:sexp* )) => `(Sexp.expr [ $ss,* ])
  | `(sexp| ( $ss:sexp* ...{ $t:term } $ts:sexp* )) => `(Sexp.expr <| [ $ss,* ] ++ ($t : List Sexp) ++ [ $ts,* ])
  | `(sexp| { $t:term }) => `($t)

syntax "sexp!{" sexp "}" : term

/-- S-expressions can be written using `sexp!{...}` syntax. -/
macro_rules
  | `(sexp!{ $s:sexp }) => `($s)

syntax "sexps!{" sexp* "}" : term
syntax "sexps!{" sexp* "...{" term "}" sexp* "}" : term
macro_rules
  | `(sexps!{ $ss:sexp* }) => do
    let ss ← ss.mapM fun s => `(sexp!{ $s })
    `([ $[$ss],* ])
  | `(sexps!{ $ss:sexp* ...{ $t:term } $ts:sexp* }) =>
    `([ $[$ss],* ] ++ ($t : List Sexp) ++ [ $[$ts],* ])

instance : Repr Sexp where
  reprPrec s _ := s!"sexp!\{{toString s}}"
