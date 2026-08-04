/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute
import Mathlib.Data.ZMod.Basic



@[smt_normalize ↓]
theorem neg_add_sub {a b : ZMod n} : a - b = a + - b := by exact sub_eq_add_neg a b
