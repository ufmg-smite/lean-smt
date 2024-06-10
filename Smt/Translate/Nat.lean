/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Qq

import Smt.Translate

namespace Smt.Translate.Nat

open Qq
open Lean Expr
open Translator Term

@[smt_translate] def translateNat : Translator := fun (e : Q(Nat)) => match e with
  | ~q(OfNat.ofNat $n) => return if let some n := n.nat? then literalT (toString n) else none
  | ~q(.zero)    => return literalT "0"
  | ~q(.succ $n) => return mkApp2 (symbolT "+") (← applyTranslators! n) (literalT "1")
  | ~q($n + $m)  => return mkApp2 (symbolT "+") (← applyTranslators! n) (← applyTranslators! m)
  | ~q($n * $m)  => return mkApp2 (symbolT "*") (← applyTranslators! n) (← applyTranslators! m)
  | ~q($n / $m)  => return mkApp2 (symbolT "div") (← applyTranslators! n) (← applyTranslators! m)
  | ~q($n % $m)  => return mkApp2 (symbolT "mod") (← applyTranslators! n) (← applyTranslators! m)
  | ~q($n - $m)  => return mkApp3 (symbolT "ite") (mkApp2 (symbolT "<=") (← applyTranslators! m) (← applyTranslators! n))
                                                  (mkApp2 (symbolT "-") (← applyTranslators! n) (← applyTranslators! m))
                                                  (literalT "0")
  | _            => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($n : Nat) < $m) => return mkApp2 (symbolT "<") (← applyTranslators! n) (← applyTranslators! m)
  | ~q(($n : Nat) ≤ $m) => return mkApp2 (symbolT "<=") (← applyTranslators! n) (← applyTranslators! m)
  | ~q(($n : Nat) ≥ $m) => return mkApp2 (symbolT ">=") (← applyTranslators! n) (← applyTranslators! m)
  | ~q(($n : Nat) > $m) => return mkApp2 (symbolT ">") (← applyTranslators! n) (← applyTranslators! m)
  | _                   => return none

/- Translates quantified expressions over natural numbers for with versions that
   ensure the quantified variables are greater than or equal to 0. For
   example, given `∀ x : Nat, p(x)`, this method returns the expr
   `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[smt_translate] def translateForalls : Translator
  | e@(forallE n t@(const ``Nat _) b bi) => do
    if e.isArrow then return none
    let tmB ← Meta.withLocalDecl n bi t (translateBody b)
    let tmGeqZero := Term.mkApp2 (symbolT ">=") (symbolT n.toString) (literalT "0")
    let tmProp := Term.mkApp2 (symbolT "=>") tmGeqZero tmB
    return forallT n.toString (symbolT "Int") tmProp
  | _ => return none
where
  translateBody (b : Expr) (x : Expr) : TranslationM Term := do
    let tmB ← applyTranslators! (b.instantiate #[x])
    modify fun s => { s with depFVars := s.depFVars.erase x.fvarId! }
    return tmB

end Smt.Translate.Nat
