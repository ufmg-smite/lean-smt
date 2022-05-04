import Lean
import Std

namespace Smt.Attribute

open Lean
open Std

/-- An extension to Lean's runtime environment to support SMT attributes.
    Maintains a set of function declarations for the `smt` tactic to utilize
    while generating the SMT query. -/
abbrev SmtExtension := SimpleScopedEnvExtension Name (HashSet Name)

/-- Adds a declaration to the set of function declarations maintained by the SMT
    environment extension. -/
def addSmtEntry (d : HashSet Name) (e : Name) : HashSet Name :=
  d.insert e

initialize smtExt : SmtExtension ← registerSimpleScopedEnvExtension {
  name     := `SmtExt
  initial  := {}
  addEntry := addSmtEntry
}

/-- Throws unexpected type error. -/
def throwUnexpectedType (t : Name) (n : Name) : AttrM Unit :=
  throwError s!"unexpected type at '{n}', `{t}` expected"

/-- Validates the tagged declaration. -/
def validate (n : Name) : AttrM Unit := do
  match (← getEnv).find? n with
  | none      => throwError s!"unknown constant '{n}'"
  | some info =>
    match info.type with
    | Expr.const c .. =>
      if c != (`Smt.Transformer) then throwUnexpectedType `Smt.Transformer n
    | _               => throwUnexpectedType `Smt.Transformer n

/-- Registers an SMT attribute with the provided name and description and links
    it against `ext`. -/
def registerSmtAttr (attrName : Name) (attrDescr : String)
  : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun decl stx attrKind => do
      trace[Smt.debug.attr] s!"attrName: {attrName}, attrDescr: {attrDescr}"
      trace[Smt.debug.attr] s!"decl: {decl}, stx: {stx}, attrKind: {attrKind}"
      Attribute.Builtin.ensureNoArgs stx
      validate decl
      setEnv (smtExt.addEntry (← getEnv) decl)
      trace[Smt.debug.attr]
        s!"transformers: {(smtExt.getState (← getEnv)).toList}"
    erase := fun declName => do
      let s := smtExt.getState (← getEnv)
      let s := s.erase declName
      modifyEnv fun env => smtExt.modifyState env fun _ => s
  }

initialize registerSmtAttr `Smt
             "Utilize this function to transform Lean expressions to SMT terms."

end Smt.Attribute
