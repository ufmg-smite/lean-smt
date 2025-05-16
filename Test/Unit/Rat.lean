import Smt
import Smt.Rat

def Lean.Expr.ratAbs? (e : Lean.Expr) : Option Expr := do
  let .app (.const ``Rat.abs _) x := e | none
  return x

def Lean.Expr.ratFloor? (e : Lean.Expr) : Option Expr := do
  let .app (.const ``Rat.floor _) x := e | none
  return x

namespace Smt.Translate.Rat

open Translator Term

private def mkRat : Lean.Expr :=
  .const ``Rat []

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Rat _  => return symbolT "Real"
  | _                => return none

@[smt_translate] def translateInt : Translator := fun e => do
  if let some x := e.ratFloor? then
    return appT (symbolT "to_int") (← applyTranslators! x)
  else
    return none

@[smt_translate] def translateRat : Translator := fun e => do
  if let some n := e.natLitOf? mkRat then
    return literalT s!"{n}.0"
  else if let some x := e.intCastOf? mkRat then
    return appT (symbolT "to_real") (← applyTranslators! x)
  else if let some x := e.negOf? mkRat then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some x := e.ratAbs? then
    return appT (symbolT "abs") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkRat mkRat then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkRat mkRat then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkRat mkRat then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkRat mkRat then
    return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkRat then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkRat then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkRat then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkRat then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Rat

example : (1 : Rat) < 2 := by
  smt

example {x : Rat} : x = 1 → x < 2 := by
  smt

example {x : Rat} : x * x ≥ 0 := by
  smt

example {x y : Rat} : x = y → x * y ≥ 0 := by
  smt

example {x₁ x₂ y₁ y₂ : Rat} (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  smt [h₁, h₂]

example {x₁ x₂ x₃ y₁ y₂ y₃ : Rat} (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) (h₃ : x₃.abs > y₃.abs) : (x₁ * x₂ * x₃).abs > (y₁ * y₂ * y₃).abs := by
  smt [h₁, h₂, h₃]
