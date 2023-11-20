/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Builtin

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/uf/rewrites

-- Equality

@[smt_simp] theorem eq_refl : (t = t) = True := eq_self t
@[smt_simp] theorem eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩

@[smt_simp] theorem distinct_binary_elim : (t ≠ s) = ¬(t = s) := rfl

end Smt.Reconstruction.Rewrites.Builtin
