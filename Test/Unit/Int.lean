import Smt

def Lean.Expr.intAbs? (e : Lean.Expr) : Option Expr := do
  let .app (.const ``Int.abs _) x := e | none
  return x

namespace Smt.Translate.Int

open Translator Term

@[smt_translate] def translateAbs : Translator := fun e => do
  if let some x := e.intAbs? then
    return appT (symbolT "abs") (← applyTranslators! x)
  else
    return none

end Smt.Translate.Int

example : ((1 : Int) < 2) := by
  smt

example {x : Int} : (x = 1) → (x < 2) := by
  smt

example {x: Int} : (x * x ≥ 0) := by
  smt

example {x y: Int} : (x = y) → (x * y ≥ 0) := by
  smt

example {x₁ x₂ y₁ y₂ : Int} (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  smt [h₁, h₂]

example {x₁ x₂ x₃ y₁ y₂ y₃ : Int} (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) (h₃ : x₃.abs > y₃.abs) : (x₁ * x₂ * x₃).abs > (y₁ * y₂ * y₃).abs := by
  smt [h₁, h₂, h₃]
