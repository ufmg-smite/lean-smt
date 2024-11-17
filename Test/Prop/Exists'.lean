import Smt

theorem exists' : ∃ p : Prop, p := by
  smt
  · intro; apply propext; apply Iff.intro
    · intro hp ht
      cases hp True <;> contradiction
    · intro hnt
      contradiction
