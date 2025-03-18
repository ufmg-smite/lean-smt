/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Basic

namespace Real

def addN : List Real → Real
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, add_assoc]
    all_goals (intro h; nomatch h)

def mulN : List Real → Real
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, mul_assoc]
    all_goals (intro h; nomatch h)

end Real
