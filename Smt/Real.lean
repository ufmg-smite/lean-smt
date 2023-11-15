/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaiyu Yang
-/

import Lean
import Smt.Translator
import Mathlib.Data.Real.Basic
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Smt.Real

open Lean Expr
open Translator Term

#check @DivInvMonoid.div'

@[smtTranslator] def replaceConst : Translator
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "add") _ => return symbolT "+"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "sub") _ => return symbolT "-"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "neg")  _ => return symbolT "-"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "mul") _ => return symbolT "*"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "div")  _ => return symbolT "div"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "lt")  _  => return symbolT "<"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "blt") _ => return symbolT "<"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "le") _ => return symbolT "<="
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "one") _ => return literalT "1"
  | const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "zero") _ => return literalT "0"
  | app (const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "inv'") _)  x => do return Term.mkApp2 (symbolT "/") (literalT "1") (← applyTranslators! x)
  | const `Real.rpow _ => return symbolT "^"
  | app (app (app (app (app (const ``npowRec _) (const `Real _)) _) _) n) a => do return Term.mkApp2 (symbolT "^") (← applyTranslators! a) (← applyTranslators! n)
  | app (app (app (const ``DivInvMonoid.div' _) (const `Real _)) _) _ => return symbolT "/"
  | lam (body := lam (body := app (app (const (Name.str (Name.str (Name.num `_private.Mathlib.Data.Real.Basic 0) "Real") "mul")  _) _) _) ..) .. => return symbolT "*"
  | app (app (const ``LE.le _) (const `Real _)) _ => return symbolT "<="
  | app (app (const ``GT.gt _) (const `Real _)) _ => return symbolT ">"
  | app (app (const ``GE.ge _) (const `Real _)) _ => return symbolT ">="
  | app (const ``Int.ofNat _) e => applyTranslators! e
  | app (app (app (const ``Nat.cast _) (const `Real _)) _) e => applyTranslators! e
  | app (app (app (const ``Int.cast _) (const `Real _)) _) e => applyTranslators! e
  | _ => return none

/-
@[smtTranslator] def replaceConst : Translator
  | const `Real _      => return symbolT "Real"
  | const `Real.add _ => return symbolT "+"
  | const `Real.sub _ => return symbolT "-"
  | const `Real.neg _ => return symbolT "-"
  | const `Real.mul _ => return symbolT "*"
  | const `Real.div _ => return symbolT "div"
  | const `Real.lt _  => return symbolT "<"
  | const `Real.blt _ => return symbolT "<"
  | app (app (const ``LE.le _) (const `Real _)) _ => return symbolT "<="
  | app (app (const ``GT.gt _) (const `Real _)) _ => return symbolT ">"
  | app (app (const ``GE.ge _) (const `Real _)) _ => return symbolT ">="
  | app (app (app (const ``Int.cast _) (const `Real _)) _) e => applyTranslators! e
  | _ => return none
-/

end Smt.Real
