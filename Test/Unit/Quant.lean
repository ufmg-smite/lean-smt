import Smt

example {U : Type} {p : U → Prop} {q : Prop} : (∀ x, p x ∨ q) = ((∀ x, p x) ∨ q) := by
  smt

example {U : Type} {p : Prop} {q : U → Prop} : (∀ x, p ∨ q x) = (p ∨ (∀ x, q x)) := by
  smt

example {U : Type} {p q r : U → Prop} : (∀ x y z, p x ∨ q y ∨ r z) = ((∀ x, p x) ∨ (∀ y, q y) ∨ (∀ z, r z)) := by
  smt

example {U : Type} {p : U → Prop} {q : U → U → Prop} {r : Prop} : (∀ x y₁ y₂, p x ∨ q y₁ y₂ ∨ r) = ((∀ x, p x) ∨ (∀ y₁ y₂, q y₁ y₂) ∨ r) := by
  smt

example {U : Type} {p : U → U → U → Prop} : (∀ x y z, p x y z) = (∀ y z x, p x y z) := by
  smt

example {U : Type} {t : U} {p : U → Prop} : (∀ y, y ≠ t ∨ p y) = p t := by
  smt

example {U : Type} {t : U} : (∀ x, x ≠ t) = False := by
  smt
