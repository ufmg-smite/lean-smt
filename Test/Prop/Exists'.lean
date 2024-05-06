import Smt

theorem exists' : ∃ p : Prop, p := by
  smt
  · intro; apply propext; apply Iff.intro
    · intro hp ht
      exact hp True ht
    · intro hnt
      contradiction
