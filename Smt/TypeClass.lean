import Lean
import Smt.Translator

namespace Smt.TypeClass

open Lean Expr
open Translator Term

@[smtTranslator] def replaceConst : Translator
  | e => sorry
