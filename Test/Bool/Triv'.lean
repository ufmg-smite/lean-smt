import Smt

theorem triv': ∀ p : Bool, ∀ _ : p, p := by
  smt_show
  intro p
  simp_all
