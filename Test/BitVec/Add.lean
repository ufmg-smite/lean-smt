import Smt

open Std.BitVec

example {x y : Std.BitVec 4} : ¬(x = 11#4 ∧ y = 11#4 ∧ x + y = 15#4) := by
  smt
  all_goals simp
  all_goals sorry

example {x y : Std.BitVec 8} : ¬(x = 11#8 ∧ y = 11#8 ∧ x + y = 15#8) := by
  smt
  all_goals simp
  all_goals sorry

example {x y : Std.BitVec 16} : ¬(x = 11#16 ∧ y = 11#16 ∧ x + y = 15#16) := by
  smt
  all_goals simp
  all_goals sorry
