/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute

@[smt_normalize ↓]
theorem Int.neg_def : Int.neg a = -a := rfl

@[smt_normalize ↓]
theorem Int.sub_def : Int.sub a b = a - b := rfl

@[smt_normalize ↓]
theorem Int.mod_def : Int.emod a b = a % b := rfl

@[smt_normalize ↓]
theorem Int.pow_def : Int.pow a b = a ^ b := rfl

@[smt_normalize ↓]
theorem Int.lt_def : Int.lt a b = (a < b) := rfl

@[smt_normalize ↓]
theorem Int.le_def' : Int.le a b = (a ≤ b) := rfl

attribute [smt_normalize ↓] Int.add_def Int.mul_def Int.div_def
  Int.ofNat_eq_natCast Int.negSucc_eq Int.cast_ofNat_Int
