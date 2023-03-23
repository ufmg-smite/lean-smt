/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Builtin

-- Equality

@[smt_simp] theorem eq_refl : (t = t) = True := eq_self t
@[smt_simp] theorem eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩

-- ITE

@[smt_simp] theorem ite_true_cond : ite True x y = x := rfl
@[smt_simp] theorem ite_false_cond : ite False x y = y := rfl
@[smt_simp] theorem ite_not_cond [h : Decidable c] : ite (Not c) x y = ite c y x :=
  h.byCases (fun hc => if_pos hc ▸ if_neg (not_not_intro hc) ▸ rfl)
            (fun hnc => if_pos hnc ▸ if_neg hnc ▸ rfl)
@[smt_simp] theorem ite_eq_branch [h : Decidable c] : ite c x x = x :=
  h.byCases (if_pos · ▸ rfl) (if_neg · ▸ rfl)

end Smt.Reconstruction.Rewrites.Builtin
