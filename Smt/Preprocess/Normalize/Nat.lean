/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute

attribute [smt_normalize ↓] Nat.zero_eq Nat.succ_eq_add_one

@[smt_normalize ↓]
theorem Nat.add_def : Nat.add a b = a + b := rfl

@[smt_normalize ↓]
theorem Nat.sub_def : Nat.sub a b = a - b := rfl

@[smt_normalize ↓]
theorem Nat.mul_def' : Nat.mul a b = a * b := rfl

@[smt_normalize ↓]
theorem Nat.div_def : Nat.div a b = a / b := rfl

@[smt_normalize ↓]
theorem Nat.mod_def' : Nat.mod a b = a % b := rfl

@[smt_normalize ↓]
theorem Nat.pow_def : Nat.pow a b = a ^ b := rfl

@[smt_normalize ↓]
theorem Nat.lt_def : Nat.lt a b = (a < b) := rfl

@[smt_normalize ↓]
theorem Nat.le_def : Nat.le a b = (a ≤ b) := rfl
