import Smt
import Smt.Real

example {x₁ x₂ y₁ y₂ : Real} (h₁ : |x₁| > |y₁|) (h₂ : |x₂| > |y₂|) : |x₁ * x₂| > |y₁ * y₂| := by
  smt [h₁, h₂]

example {x₁ x₂ x₃ y₁ y₂ y₃ : Real} (h₁ : |x₁| > |y₁|) (h₂ : |x₂| > |y₂|) (h₃ : |x₃| > |y₃|) : |x₁ * x₂ * x₃| > |y₁ * y₂ * y₃| := by
  smt [h₁, h₂, h₃]
