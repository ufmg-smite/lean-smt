import Smt

theorem triv': ∀ p : Prop, p → p := by
  smt
  apply propext
  apply Iff.intro
  · exact λ _ _ => id
  · exact λ _   => True.intro
