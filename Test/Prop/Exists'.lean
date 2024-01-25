import Smt

theorem exists' : ∃ p : Prop, p := by
  smt
  · intro; apply propext; apply Iff.intro
    · intro ⟨p, hp⟩ hnp
      exact hnp p hp
    · intro
      exact ⟨True, True.intro⟩
  · intro; apply propext; apply Iff.intro
    · intro hnp
      exact hnp True
    · intro hf
      contradiction
