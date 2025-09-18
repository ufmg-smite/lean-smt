/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean

import Smt.Attribute
import Smt.Translate.Term

/-- Return true iff `e` contains a free variable which satisfies `p`. -/
@[inline] private def Lean.Expr.hasAnyFVar' [Monad m] (e : Expr) (p : FVarId → m Bool) : m Bool :=
  let rec @[specialize] visit (e : Expr) := do if !e.hasFVar then return false else
    match e with
    | Expr.forallE _ d b _   => return (← visit d) || (← visit b)
    | Expr.lam _ d b _       => return (← visit d) || (← visit b)
    | Expr.mdata _ e         => visit e
    | Expr.letE _ t v b _    => return (← visit t) || (← visit v) || (← visit b)
    | Expr.app f a           => return (← visit f) || (← visit a)
    | Expr.proj _ _ e        => visit e
    | Expr.fvar fvarId       => p fvarId
    | _                      => return false
  visit e

namespace Smt

open Lean Meta Expr
open Attribute Term

structure TranslationM.State where
  /-- Constants that the translated result depends on. We propagate these upwards during translation
  in order to build a dependency graph. The value is reset at the `translateExpr` entry point. -/
  depConstants : NameSet := {}
  /-- Free variables that the translated result depends on. We propagate these upwards during translation
  in order to build a dependency graph. The value is reset at the `translateExpr` entry point. -/
  depFVars : FVarIdSet := {}
  /-- Free variables introduced during translation (from binder expressions). Those should NOT be
  propegated upwards during translation. -/
  localFVars : FVarIdSet := {}
  /-- Memoizes `applyTranslators?` calls together with what they add to `depConstants` and `depFVars`. -/
  cache : Std.HashMap Expr (Option (Term × NameSet × FVarIdSet)) := {}
  /-- A mapping from a scopped name to a suffix index that makes it unique. This field does not handle
  scopping, which should be handled by `withScopedName` -/
  scopedNames : Std.HashMap Name Nat := {}
  /-- A mapping from fvars to unique names. -/
  uniqueFVarNames : Std.HashMap FVarId String := {}

abbrev TranslationM := StateT TranslationM.State MetaM

/-- A function which translates some subset of Lean expressions to SMT-LIBv2 `Term`s. We use
the combination of all registered translators to encode a fragment of Lean into the many-sorted
first-order logic of SMT-LIBv2. New translators can be registered with the `smt_translate` attribute.

The input expression is guaranteed to be well-typed in the `MetaM` context. The return value is:
- `some t` when the translator supports the input and translates it to `t`
- `none` when the translator doesn't support the input -/
abbrev Translator := Expr → TranslationM (Option Term)

namespace Translator

private unsafe def getTranslatorsUnsafe : MetaM (List (Translator × Name)) := do
  let env ← getEnv
  let names := ((smtExt.getState env).getD ``Translator {}).toList
  -- trace[smt.attr] "Translators: {names}"
  let mut translators := []
  for name in names do
    let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConst Translator Options.empty name
    translators := (fn, name) :: translators
  return translators

/-- Returns the list of translators maintained by `smtExt` in the current
    Lean environment. -/
@[implemented_by getTranslatorsUnsafe]
opaque getTranslators : MetaM (List (Translator × Name))

/-- Return a cached translation of `e` if found, otherwise run `k e` and cache the result. -/
def withCache (k : Translator) (e : Expr) : TranslationM (Option Term) := do
  match (← get).cache[e]? with
  | some (some (tm, depConsts, depFVars)) =>
    modify fun st => { st with
      depConstants := st.depConstants ∪ depConsts
      depFVars := st.depFVars.union depFVars
    }
    return some tm
  | some none =>
    return none
  | none =>
    let depConstantsBefore := (← get).depConstants
    let depFVarsBefore := (← get).depFVars
    modify fun st => { st with depConstants := .empty, depFVars := .empty }
    let ret? ← k e
    modify fun st => { st with
      depConstants := st.depConstants ∪ depConstantsBefore
      depFVars := st.depFVars.union depFVarsBefore
      cache := st.cache.insert e <| ret?.map ((·, st.depConstants, st.depFVars))
    }
    return ret?

def withScopedName (n : Name) (b : Expr) (k : Name → TranslationM α) : TranslationM α := do
  let state ← get
  let mut n' := n
  let mut scopedNames := state.scopedNames
  while ← b.hasAnyFVar' (·.getUserName >>= (return · == n')) do
    let i := scopedNames.getD n 1
    n' := n.appendIndexAfter i
    scopedNames := scopedNames.insert n (i + 1)
  set { state with scopedNames := scopedNames }
  let k := k n'
  set state
  k

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
          trace[smt.translate.expr] "{e} =({nm})=> {tm}"
          return tm

      -- Then try splitting subexpressions
      match e with
      | fvar fv =>
        if (← get).localFVars.contains fv then
          return symbolT (← fv.getUserName).toString
        else
          modify fun st => { st with depFVars := st.depFVars.insert fv }
          match (← get).uniqueFVarNames[fv]? with
          | some n => return symbolT n
          | none   => return symbolT (← fv.getUserName).toString
      | const nm _ =>
        modify fun st => { st with depConstants := st.depConstants.insert nm }
        return symbolT nm.toString
      | app f e => return appT (← applyTranslators! f) (← applyTranslators! e)
      | lam .. => throwError "cannot translate {e}, SMT-LIB does not support lambdas"
      | forallE n t b bi => withScopedName n b fun n => do
        let tmB ← Meta.withLocalDecl n bi t (translateBody b)
        if !b.hasLooseBVars /- not a dependent arrow -/ then
          return arrowT (← applyTranslators! t) tmB
        else
          return forallT n.toString (← applyTranslators! t) tmB
      | letE n t v b _ =>
        let tmB ← Meta.withLetDecl n t v (translateBody b)
        return letT n.toString (← applyTranslators! v) tmB
      | mdata _ e => go ts e
      | e         => throwError "cannot translate {e}"
    translateBody (b : Expr) (x : Expr) : TranslationM Term := do
      modify fun s => { s with localFVars := s.localFVars.insert x.fvarId! }
      let tmB ← applyTranslators! (b.instantiate #[x])
      modify fun s => { s with localFVars := s.localFVars.erase x.fvarId! }
      return tmB

end

def traceTranslation (e : Expr) (e' : Except ε (Term × NameSet × FVarIdSet)) : TranslationM MessageData :=
  return m!"{e} ↦ " ++ match e' with
    | .ok (e', _) => m!"{e'}"
    | .error _    => m!"{bombEmoji}"

/-- Processes `e` by running it through all the registered `Translator`s.
Returns the resulting SMT-LIB term and set of dependencies. -/
def translateExpr (e : Expr) : TranslationM (Term × NameSet × FVarIdSet) :=
  withTraceNode `smt.translate (traceTranslation e ·) do
    modify fun st => { st with depConstants := .empty, depFVars := .empty }
    trace[smt.translate.expr] "before: {e}"
    let tm ← applyTranslators! e
    trace[smt.translate.expr] "translated: {tm}"
    return (tm, (← get).depConstants, (← get).depFVars)

def translateExpr' (e : Expr) : TranslationM Term :=
  Prod.fst <$> translateExpr e

end Smt.Translator
