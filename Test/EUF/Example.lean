import Smt

example [Nonempty U] {f : U → U → U} {a b c d : U} : (a = b) → (c = d) → p1 ∧ True → (¬ p1) ∨ (p2 ∧ p3) → (¬ p3) ∨ (¬ (f a c = f b d)) → False := by
  smt

example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3)) (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [*]
