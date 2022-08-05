/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean

import Smt.Term
import Smt.Util
import Smt.Attribute

namespace Smt

open Lean Meta Expr
open Attribute Term

structure TranslationM.State where
  /-- Constants that the translated result depends on. We propagate these upwards during translation
  in order to build a dependency graph. The value is reset at the `translateExpr` entry point. -/
  depConstants : NameSet := .empty
  /-- Memoizes `applyTranslators?` calls together with what they add to `depConstants`. -/
  cache : Std.HashMap Expr (Option (Term × NameSet)) := .empty

abbrev TranslationM := StateT TranslationM.State MetaM

/-- A function which translates some subset of Lean expressions to SMT-LIBv2 `Term`s. We use
the combination of all registered translators to encode a fragment of Lean into the many-sorted
first-order logic of SMT-LIBv2. New translators can be registered with the `smtTranslator` attribute.

The input expression is guaranteed to be well-typed in the `MetaM` context. The return value is:
- `some t` when the translator supports the input and translates it to `t`
- `none` when the translator doesn't support the input -/
abbrev Translator := Expr → TranslationM (Option Term)

namespace Translator

private unsafe def getTranslatorsUnsafe : MetaM (List (Translator × Name)) := do
  let env ← getEnv
  let names := (smtExt.getState env).toList
  -- trace[smt.debug.attr] "Translators: {names}"
  let mut translators := []
  for name in names do
    let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConst Translator Options.empty name
    translators := (fn, name) :: translators
  return translators

/-- Returns the list of translators maintained by `smtExt` in the current
    Lean environment. -/
@[implementedBy getTranslatorsUnsafe]
opaque getTranslators : MetaM (List (Translator × Name))

/-- Return a cached translation of `e` if found, otherwise run `k e` and cache the result. -/
def withCache (k : Translator) (e : Expr) : TranslationM (Option Term) := do
  match (← get).cache.find? e with
  | some (some (tm, deps)) =>
    modify fun st => { st with depConstants := st.depConstants.union deps }
    return some tm
  | some none =>
    return none
  | none =>
    let depConstantsBefore := (← get).depConstants
    modify fun st => { st with depConstants := .empty }
    let ret? ← k e
    modify fun st => { st with
      depConstants := st.depConstants.union depConstantsBefore
      cache := st.cache.insert e <| ret?.map ((·, st.depConstants))
    }
    return ret?

mutual

/-- Like `applyTranslators?` but must succeed. -/
partial def applyTranslators! (e : Expr) : TranslationM Term := do
  let some tm ← applyTranslators? e | throwError "no translator matched {e}"
  return tm

/-- Traverses `e` to compute its SMT-LIB translation. First all translators are tried on the whole
expression and if one succeeds, its result is returned. Otherwise, `e` is split into subexpressions
which are then recursively translated and put together into an SMT-LIB term. The traversal proceeds
in a top-down, depth-first order. -/
partial def applyTranslators? : Translator := withCache fun e => do
  let ts ← getTranslators
  go ts e
  where
    go (ts : List (Translator × Name)) : Translator := fun e => do
      -- First try all translators on the whole expression
      -- TODO: Use `DiscrTree` to index the translators instead of naively looping
      for (t, nm) in ts do
        if let some tm ← t e then
          trace[smt.debug.translator] "{e} =({nm})=> {tm}"
          return tm

      -- Then try splitting subexpressions
      match e with
      | fvar fv =>
        let ld ← Meta.getLocalDecl fv
        return symbolT ld.userName.toString
      | const nm _ =>
        modify fun st => { st with depConstants := st.depConstants.insert nm }
        return symbolT nm.toString
      | app f e => return appT (← applyTranslators! f) (← applyTranslators! e)
      | lam .. => throwError "cannot translate {e}, SMT-LIB does not support lambdas"
      | forallE n t b bi =>
        let tmB ← Meta.withLocalDecl n bi t (fun x => applyTranslators! <| b.instantiate #[x])
        if !b.hasLooseBVars /- not a dependent arrow -/ then
          return arrowT (← applyTranslators! t) tmB
        else
          return forallT n.toString (← applyTranslators! t) tmB
      | letE n t v b _ =>
        let tmB ← Meta.withLetDecl n t v (fun x => applyTranslators! <| b.instantiate #[x])
        return letT n.toString (← applyTranslators! v) tmB
      | mdata _ e => go ts e
      | e         => throwError "cannot translate {e}"

end

/-- Processes `e` by running it through all the registered `Translator`s.
Returns the resulting SMT-LIB term and set of dependencies. -/
def translateExpr (e : Expr) : TranslationM (Term × NameSet) :=
  traceCtx `smt.debug.translateExpr do
    modify fun st => { st with depConstants := .empty }
    trace[smt.debug.translator] "before: {e}"
    let e ← Util.unfoldAllProjInsts e
    trace[smt.debug.translator] "after unfolding projs: {e}"
    let tm ← applyTranslators! e
    trace[smt.debug.translator] "translated: {tm}"
    return (tm, (← get).depConstants)

def translateExpr' (e : Expr) : TranslationM Term :=
  Prod.fst <$> translateExpr e

end Smt.Translator
