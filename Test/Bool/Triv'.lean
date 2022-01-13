import Smt

theorem triv': ∀ p : Bool, ∀ _ : p, p := by
  smt
  intro p
  simp_all
