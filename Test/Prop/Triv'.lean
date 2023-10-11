import Smt

theorem triv': ∀ p : Prop, p → p := by
  smt
  apply propext
  apply Iff.intro
  · exact λ _ _ => (Classical.em _).symm
  · exact λ _   => True.intro
