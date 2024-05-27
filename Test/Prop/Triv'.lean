import Smt

example : ∀ p : Prop, p → p := by
  smt
  all_goals
    intros; apply propext; apply Iff.intro
    · intros; trivial
    · intros; simp_all
