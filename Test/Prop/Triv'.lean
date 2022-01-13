import Smt

theorem triv': ∀ p : Prop, ∀ _ : p, p := by
  smt
  intro p
  simp_all
