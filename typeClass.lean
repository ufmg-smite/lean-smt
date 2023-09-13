import Smt

import Lean

import Mathlib

open Lean Meta Elab Tactic


/- #check Semigroup.toMul -/

/- syntax (name := test) "test" term : tactic -/

/- @[tactic test] def evalTest : Tactic := fun stx => -/
/-   withMainContext do -/
/-     let e ← elabTerm stx[1] none -/
/-     logInfo m!"pre e = {repr e}" -/
/-     let e ← Smt.Util.unfoldAllProjInsts e -/
/-     logInfo m!"pos e = {repr e}" -/

/- #check @Mul.mul -/

/- example (a b : Bool) [Semigroup Bool] : True := by -/
/-   test (a * b) -/
/-   admit -/

/- example [Semigroup Bool] (a b c : Bool) : -/
/-     Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by -/

  /- concretize [Mul.mul] -- solves the polymorphism over Mul.mul -/
  -- still need to remove the typeclass application

  /- smt -/

/- example (a b : Int) : Mul.mul a b = Mul.mul b a := -/
/-   by smt -/



/- #elab ∀ [Semigroup Bool] (a b c : Bool) , (a * b) * c = a * (b * c) -/

/- #eval show MetaM Unit from do -/
/-   let env ← getEnv -/
/-   let nm := ``Semigroup.toMul -/
/-   let some decl := env.find? nm | throwError "" -/
/-   /1- IO.println s!"decl.type = {decl.type}" -1/ -/
/-   let blah := getStructureInfo? env nm -/
/-   IO.println s!"{blah.isSome}" -/
/-   pure () -/

/- set_option trace.smt.debug.reconstruct true -/

/- def g : ConstantInfo → String -/
/-   | ConstantInfo.axiomInfo  _ => "1" -/
/-   | ConstantInfo.defnInfo   _ => "2" -/ 
/-   | ConstantInfo.thmInfo    _ => "3" -/ 
/-   | ConstantInfo.opaqueInfo _ => "4" -/ 
/-   | ConstantInfo.quotInfo   _ => "5" -/ 
/-   | ConstantInfo.inductInfo _ => "6" -/ 
/-   | ConstantInfo.ctorInfo   _ => "7" -/ 
/-   | ConstantInfo.recInfo    _ => "8" -/ 

/- #eval show MetaM Unit from do -/
/-   let env ← getEnv -/
/-   let some st := getStructureInfo? env ``Semigroup | throwError "" -/
/-   IO.println s!"st = {st.structName}" -/
/-   for f in st.fieldInfo do -/
/-     IO.println s!"name = {f.projFn}" -/
/-   pure () -/

/- def f : ConstantInfo → Option InductiveVal -/
/-   | ConstantInfo.inductInfo v => some v -/
/-   | _   => none -/

/- def h : ConstantInfo → Option ConstructorVal -/
/-   | ConstantInfo.ctorInfo v => some v -/
/-   | _ => none -/

#eval show MetaM Unit from do
  let env ← getEnv
  let some decl := env.find? ``Monoid | throwError "err 1"
  pure ()
/-   let some indVal := f decl | throwError "err 2" -/
/-   let [ctor] := indVal.ctors | throwError "err 3" -/
/-   let some decl2 := env.find? ctor | throwError "err 4" -/
/-   let some ctorVal := h decl2 | throwError "err 5" -/
/-   IO.println s!"ctorVal.type = {ctorVal.type}" -/
/-   pure () -/



  
