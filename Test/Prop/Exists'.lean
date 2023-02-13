import Smt

theorem exists' : ∃ p : Prop, p := by
  smt
  · apply propext
    apply Iff.intro
    · intro ⟨p, hp⟩ hnp
      exact hnp p hp
    · intro
      exact ⟨True, True.intro⟩
  · apply propext
    apply Iff.intro
    · intro hf
      contradiction
    · intro hnp
      exact hnp True True.intro
