/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Prop.Core

namespace Smt.Reconstruct.Bool

theorem decide_true_eq : decide True = true := rfl

theorem decide_false_eq : decide False = false := rfl

theorem decide_not_eq [hp: Decidable p] : decide (¬p) = !(decide p) :=
  match hp with
  | isFalse _ => rfl
  | isTrue  _ => rfl

theorem decide_and_eq [hp: Decidable p] [hq: Decidable q] : decide (p ∧ q) = (decide p && decide q) :=
  match hp, hq with
  | isFalse _, isFalse _ => rfl
  | isFalse _, isTrue _  => rfl
  | isTrue  _, isFalse _ => rfl
  | isTrue  _, isTrue _  => rfl

theorem decide_or_eq [hp: Decidable p] [hq: Decidable q] : decide (p ∨ q) = (decide p || decide q) :=
  match hp, hq with
  | isFalse _, isFalse _ => rfl
  | isFalse _, isTrue _  => rfl
  | isTrue  _, isFalse _ => rfl
  | isTrue  _, isTrue _  => rfl

theorem decide_eq_eq [hp: Decidable p] [hq: Decidable q] : decide (p = q) = (decide p == decide q) :=
  match hp, hq with
  | isFalse _, isFalse _ => rfl
  | isFalse _, isTrue _  => rfl
  | isTrue  _, isFalse _ => rfl
  | isTrue  _, isTrue _  => rfl

theorem decide_xor_eq [hp: Decidable p] [hq: Decidable q] : decide (XOr p q) = Bool.xor (decide p) (decide q) :=
  match hp, hq with
  | isFalse _, isFalse _ => rfl
  | isFalse _, isTrue _  => rfl
  | isTrue  _, isFalse _ => rfl
  | isTrue  _, isTrue _  => rfl

theorem eq_of_decide_eq [hp : Decidable p] [hq : Decidable q] (_ : decide p = decide q) : p = q :=
  match hp, hq with
  | .isFalse hnp, .isFalse hnq => propext ⟨fun hp => False.elim (hnp hp), fun hq => False.elim (hnq hq)⟩
  | .isTrue hp, .isTrue hq     => propext ⟨fun _ => hq, fun _ => hp⟩

end Smt.Reconstruct.Bool
