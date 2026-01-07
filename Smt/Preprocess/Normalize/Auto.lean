/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute
import Auto.Lib.BoolExtra

namespace Auto.Bool

@[smt_normalize ↓]
theorem ofProp_def [Decidable p] : ofProp p = decide p := by
  by_cases h : p <;> simp [Bool.ofProp_spec, Bool.ofProp_spec', h]

@[smt_normalize ↓ low]
theorem ofProp_def' : ofProp p = @decide p (@Classical.propDecidable p) := by
  by_cases h : p <;> simp [Bool.ofProp_spec, Bool.ofProp_spec', h]

@[smt_normalize ↓]
theorem ite'_def [Decidable c] : ite' c t e = if c then t else e :=
  Bool.ite_simp ▸ rfl

@[smt_normalize ↓ low]
theorem ite'_def' : ite' c t e = @ite _ c (@Classical.propDecidable c) t e :=
  Bool.ite_simp ▸ rfl

end Auto.Bool
