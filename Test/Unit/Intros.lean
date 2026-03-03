import Smt

example : ∀ {U : Type → Type} [∀ T, Nonempty (U T)] {T : Type} [Nonempty T] (f : U T → T) (x : U T),
  f x = f x := by
    smt
