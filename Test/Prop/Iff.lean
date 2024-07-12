import Smt

variable {node : Type} [Nonempty node]

example (a : node → Prop) (h : ∀ n, a n ↔ a n) : ∀ n, a n ↔ a n := by
  smt [h]
