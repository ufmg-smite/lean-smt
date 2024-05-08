/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

namespace Smt.Attribute

open Lean
open Std

/-- An extension to Lean's runtime environment to support SMT attributes.
    Maintains a set of function declarations for the `smt` tactic to utilize
    while generating the SMT query. -/
abbrev SmtExtension := SimpleScopedEnvExtension (Name × Name) (HashMap Name (HashSet Name))

/-- Adds a declaration to the set of function declarations maintained by the SMT
    environment extension. -/
def addSmtEntry (d : HashMap Name (HashSet Name)) (e : (Name × Name)) :=
  d.insert e.fst ((d.findD e.fst {}).insert e.snd)

initialize smtExt : SmtExtension ← registerSimpleScopedEnvExtension {
  name     := `SmtExt
  initial  := {}
  addEntry := addSmtEntry
}

/-- Throws unexpected type error. -/
def throwUnexpectedType (t : Name) (n : Name) : AttrM Unit :=
  throwError s!"unexpected type at '{n}', `{t}` expected"

/-- Validates the tagged declaration. -/
def validate (n : Name) (t : Name) : AttrM Unit := do
  match (← getEnv).find? n with
  | none      => throwError s!"unknown constant '{n}'"
  | some info =>
    match info.type with
    | Expr.const c .. => if c != t then throwUnexpectedType t n
    | _               => throwUnexpectedType t n

/-- Registers an SMT attribute with the provided name and description and links
    it against `ext`. -/
def registerSmtAttr (attrName : Name) (typeName : Name) (attrDescr : String)
  : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun decl stx attrKind => do
      trace[smt.attr] s!"attrName: {attrName}, attrDescr: {attrDescr}"
      trace[smt.attr] s!"decl: {decl}, stx: {stx}, attrKind: {attrKind}"
      Attribute.Builtin.ensureNoArgs stx
      validate decl typeName
      setEnv (smtExt.addEntry (← getEnv) (typeName, decl))
    erase := fun declName => do
      let s := smtExt.getState (← getEnv)
      let s := s.erase declName
      modifyEnv fun env => smtExt.modifyState env fun _ => s
  }

initialize registerSmtAttr `smt_translate `Smt.Translator
             "Utilize this function to translate Lean expressions to SMT terms."

initialize registerSmtAttr `smt_sort_reconstruct `Smt.SortReconstructor
             "Utilize this function to translate cvc5 sorts to Lean expressions."

initialize registerSmtAttr `smt_term_reconstruct `Smt.TermReconstructor
             "Utilize this function to translate cvc5 terms to Lean expressions."

initialize registerSmtAttr `smt_proof_reconstruct `Smt.ProofReconstructor
             "Utilize this function to translate cvc5 proofs to Lean expressions."

end Smt.Attribute
