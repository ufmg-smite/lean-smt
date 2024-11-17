/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt.Reconstruct.Builtin

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

-- ITE

theorem ite_true_cond : ite True x y = x := rfl
theorem ite_false_cond : ite False x y = y := rfl
theorem ite_not_cond [h : Decidable c] : ite (¬c) x y = ite c y x :=
  h.byCases (fun hc => if_pos hc ▸ if_neg (not_not_intro hc) ▸ rfl)
            (fun hnc => if_pos hnc ▸ if_neg hnc ▸ rfl)
theorem ite_eq_branch [h : Decidable c] : ite c x x = x :=
  h.byCases (if_pos · ▸ rfl) (if_neg · ▸ rfl)

theorem ite_then_lookahead [h : Decidable c] : ite c (ite c x y) z = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_lookahead [h : Decidable c] : ite c x (ite c y z) = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_then_neg_lookahead [h : Decidable c] : ite c (ite (¬c) x y) z = ite c y z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ ite_not_cond (c := c) ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_neg_lookahead [h : Decidable c] : ite c x (ite (¬c) y z) = ite c x y :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ ite_not_cond (c := c) ▸ if_neg hc ▸ rfl)

end Smt.Reconstruct.Builtin
