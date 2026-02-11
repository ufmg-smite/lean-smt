/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Preprocess.Normalize.Attribute

@[smt_normalize ↓]
theorem iff_eq_eq : (p ↔ q) = (p = q) := propext ⟨propext, (· ▸ ⟨(·), (·)⟩)⟩

attribute [smt_normalize ↓] dite_eq_ite

@[smt_normalize ↓]
theorem classical_ite_cond_congr [hc : Decidable c] {x y : α} :
  @ite α c (Classical.propDecidable c) x y = @ite α c hc x y := by
  simp
