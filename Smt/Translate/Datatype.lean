/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Translate
import Smt.Util

namespace Smt.Translate.Datatype

open Translator Term Lean

/-- Inductive types that have dedicated translators and should not be handled
as generic SMT-LIB datatypes. -/
private def builtinInductives : Std.HashSet Name :=
  Std.HashSet.ofList [
    ``Bool, ``True, ``False,
    ``Or, ``And, ``Iff, ``Exists,
    ``Nat, ``Int, ``String, ``BitVec
  ]

/-- Translate a constructor of a simple (non-parametric) inductive type.
The inductive type itself is marked as a dependency so that the query builder will emit a
`declare-datatypes` command for it. Constructor arguments are translated recursively.

Constructors of parametric inductives, indexed inductives, or inductives whose sort name is
already known to SMT-LIB (e.g. `Bool`) are left to other translators or the fallthrough
mechanism. Only fully applied constructors are handled. -/
@[smt_translate] def translateConstructor : Translator := fun e => do
  let some (v, args) ← Lean.Meta.constructorApp? e | return none
  let env ← getEnv
  let inductName := v.induct
  -- Skip types that SMT-LIB already knows about or that have dedicated translators.
  if Util.smtConsts.contains inductName.toString then return none
  if builtinInductives.contains inductName then return none
  -- Only handle simple non-parametric, non-indexed inductives.
  let some (.inductInfo iVal) := env.find? inductName | return none
  if iVal.numParams != 0 || iVal.numIndices != 0 then return none
  -- Only handle fully applied constructors.
  if args.size != v.numFields then return none
  -- Mark the inductive type as a dependency; the query builder will declare it.
  modify fun st => { st with depConstants := st.depConstants.insert inductName }
  -- Translate constructor arguments and build the application.
  let translatedArgs ← args.mapM applyTranslators!
  return some (translatedArgs.foldl appT (symbolT v.name.toString))

end Smt.Translate.Datatype
