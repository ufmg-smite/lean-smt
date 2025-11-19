import Smt

example : ∀ x, 0 - x = 0 := by
  intro x
  induction x with
  | zero => smt
  | succ x ih => smt [ih]
