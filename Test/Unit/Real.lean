import Smt
import Smt.Real

example : ((1 : Real) < 2) := by
  smt

example {x : Real} : (x = 1) → (x < 2) := by
  smt

example {x: Real} : (x * x ≥ 0) := by
  smt

example {x y: Real} : (x = y) → (x * y ≥ 0) := by
  smt

example {x₁ x₂ y₁ y₂ : Real} (h₁ : |x₁| > |y₁|) (h₂ : |x₂| > |y₂|) : |x₁ * x₂| > |y₁ * y₂| := by
  smt [h₁, h₂]

example {x₁ x₂ x₃ y₁ y₂ y₃ : Real} (h₁ : |x₁| > |y₁|) (h₂ : |x₂| > |y₂|) (h₃ : |x₃| > |y₃|) : |x₁ * x₂ * x₃| > |y₁ * y₂ * y₃| := by
  smt [h₁, h₂, h₃]
