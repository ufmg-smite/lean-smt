/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute

@[smt_normalize ↓]
theorem Rat.neg_def' : Rat.neg a = -a := rfl

@[smt_normalize ↓]
theorem Rat.add_def'' : Rat.add a b = a + b := rfl

@[smt_normalize ↓]
theorem Rat.sub_def'' : Rat.sub a b = a - b := rfl

@[smt_normalize ↓]
theorem Rat.mul_def'' : Rat.mul a b = a * b := rfl

@[smt_normalize ↓]
theorem Rat.div_def'' : Rat.div a b = a / b := rfl
