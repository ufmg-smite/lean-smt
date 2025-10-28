/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Abdalrhman Mohamed
-/

import Lean.PrettyPrinter.Formatter
import Lean.PrettyPrinter.Parenthesizer

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
      mkNodeToken `generalIdent startPos true c s }

def Lean.TSyntax.getGeneralId : TSyntax `generalIdent → String
  | ⟨.node _ `generalIdent args⟩ => args[0]!.getAtomVal
  | _ => unreachable!

@[combinator_formatter generalIdent] def generalIdent.formatter : Formatter := pure ()
@[combinator_parenthesizer generalIdent] def generalIdent.parenthesizer : Parenthesizer := pure ()
end

instance : ToSexp String := ⟨Sexp.atom⟩

instance [ToSexp α] : CoeOut α Sexp := ⟨ToSexp.toSexp⟩

declare_syntax_cat sexp
declare_syntax_cat slist

syntax generalIdent : sexp
syntax "(" ")" : sexp
syntax "(" slist ")" : sexp
syntax "{" term "}" : sexp

syntax sexp : slist
syntax "...{" term "}" : slist
syntax sexp slist : slist
syntax "...{" term "}" slist : slist

syntax "sexp!{" sexp "}" : term
syntax "slist!{" slist "}" : term

macro_rules
  | `(slist| $s:sexp) => `([sexp!{$s}])
  | `(slist| ...{ $t:term }) => `(($t : List Sexp))
  | `(slist| $s:sexp $ss:slist) => `(sexp!{$s} :: slist!{$ss})
  | `(slist| ...{ $t:term } $ss:slist) => `(($t : List Sexp) ++ slist!{$ss})

macro_rules
  | `(sexp| $a:generalIdent) => `(Sexp.atom $(Lean.quote a.getGeneralId))
  | `(sexp| ()) => `(Sexp.expr [])
  | `(sexp| ( $ss:slist )) => `(Sexp.expr slist!{$ss})
  | `(sexp| { $t:term }) => `(($t : Sexp))

/-- S-expressions can be written using `sexp!{...}` syntax. -/
macro_rules
  | `(sexp!{ $s:sexp }) => `(sexp|$s)
  | `(slist!{ $ss:slist }) => `(slist|$ss)

syntax "sexps!{" "}" : term
syntax "sexps!{" slist "}" : term
macro_rules
  | `(sexps!{ }) => `(([] : List Sexp))
  | `(sexps!{ $ss:slist }) => `(slist!{$ss})

instance : Repr Sexp where
  reprPrec s _ := s!"sexp!\{{toString s}}"

/-- info: sexp!{()} -/
#guard_msgs in #eval sexp!{()}
/-- info: sexp!{foo} -/
#guard_msgs in #eval sexp!{foo}
/-- info: sexp!{foo} -/
#guard_msgs in #eval sexp!{{Sexp.atom "foo"}}
/-- info: sexp!{(foo)} -/
#guard_msgs in #eval sexp!{(foo)}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(foo bar)}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(foo {Sexp.atom "bar"})}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{({Sexp.atom "foo"} bar)}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(foo ...{[Sexp.atom "bar"]})}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(...{[Sexp.atom "foo"]} bar)}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(...{[Sexp.atom "foo"]} ...{[Sexp.atom "bar"]})}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{(...{[Sexp.atom "foo", Sexp.atom "bar"]})}
/-- info: sexp!{(foo bar)} -/
#guard_msgs in #eval sexp!{{Sexp.expr [Sexp.atom "foo", Sexp.atom "bar"]}}
/-- info: [] -/
#guard_msgs in #eval sexps!{}
/-- info: [sexp!{()}] -/
#guard_msgs in #eval sexps!{()}
/-- info: [sexp!{()}, sexp!{()}] -/
#guard_msgs in #eval sexps!{() ()}
