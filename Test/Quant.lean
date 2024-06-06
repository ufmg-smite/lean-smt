import Smt

example {U : Type} [Nonempty U] {p : U → Prop} :
  (∀ x y z, p x ∧ p y ∧ p z) = ((∀ x, p x) ∧ (∀ y, p y) ∧ (∀ z, p z)) := by
  smt
