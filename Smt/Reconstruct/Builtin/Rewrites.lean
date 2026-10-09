/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

@[expose] public section

namespace Smt.Reconstruct.Builtin

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

-- ITE

theorem ite_true_cond : ite True x y = x := rfl
theorem ite_false_cond : ite False x y = y := rfl
theorem ite_not_cond [h : Decidable c] : ite (¬c) x y = ite c y x :=
  h.byCases (fun hc => ite_eq_left hc ▸ ite_eq_right (not_not_intro hc) ▸ rfl)
            (fun hnc => ite_eq_left hnc ▸ ite_eq_right hnc ▸ rfl)
theorem ite_eq_branch [h : Decidable c] : ite c x x = x :=
  h.byCases (ite_eq_left · ▸ rfl) (ite_eq_right · ▸ rfl)

theorem ite_then_lookahead [h : Decidable c] : ite c (ite c x y) z = ite c x z :=
  h.byCases (fun hc => ite_eq_left hc ▸ ite_eq_left hc ▸ ite_eq_left hc ▸ rfl)
            (fun hc => ite_eq_right hc ▸ ite_eq_right hc ▸ rfl)
theorem ite_else_lookahead [h : Decidable c] : ite c x (ite c y z) = ite c x z :=
  h.byCases (fun hc => ite_eq_left hc ▸ ite_eq_left hc ▸ rfl)
            (fun hc => ite_eq_right hc ▸ ite_eq_right hc ▸ ite_eq_right hc ▸ rfl)
theorem ite_then_neg_lookahead [h : Decidable c] : ite c (ite (¬c) x y) z = ite c y z :=
  h.byCases (fun hc => ite_eq_left hc ▸ ite_eq_left hc ▸ ite_not_cond (c := c) ▸ ite_eq_left hc ▸ rfl)
            (fun hc => ite_eq_right hc ▸ ite_eq_right hc ▸ rfl)
theorem ite_else_neg_lookahead [h : Decidable c] : ite c x (ite (¬c) y z) = ite c x y :=
  h.byCases (fun hc => ite_eq_left hc ▸ ite_eq_left hc ▸ rfl)
            (fun hc => ite_eq_right hc ▸ ite_eq_right hc ▸ ite_not_cond (c := c) ▸ ite_eq_right hc ▸ rfl)

end Smt.Reconstruct.Builtin
