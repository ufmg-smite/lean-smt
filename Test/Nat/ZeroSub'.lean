import Smt

/- theorem zero_sub : ∀ x, 0 - x = 0 := by
  smt
  intro x
  induction x <;> /- smt <;> -/ simp_all [Nat.sub_succ]
-/
