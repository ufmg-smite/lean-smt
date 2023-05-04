import Smt

example : ∀ x, 0 - x = 0 := by
  intro x
  induction x with
  | zero => smt; rfl
  | succ x ih => smt [ih]; simp [ih, Nat.sub_succ]
