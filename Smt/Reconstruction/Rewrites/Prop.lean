/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruction.Rewrites.Simp

namespace Smt.Reconstruction.Rewrites.Prop

scoped notation "const " c => fun _ => c

@[smt_simp] theorem bool_double_neg_elim [Decidable t] : Not (Not t) = t :=
  propext ⟨Decidable.of_not_not, not_not_intro⟩

@[smt_simp] theorem bool_eq_true : (t = True) = t :=
  propext ⟨of_eq_true, eq_true⟩
@[smt_simp] theorem bool_eq_false : (t = False) = (Not t) :=
  propext ⟨(· ▸ not_false), eq_false⟩

@[smt_simp] theorem bool_impl_false1 : (t → False) = (Not t) :=
  propext ⟨(·), (·)⟩
@[smt_simp] theorem bool_impl_false2 : (False → t) = True :=
  propext ⟨const trivial, const False.elim⟩
@[smt_simp] theorem bool_impl_true1 : (t → True) = True :=
  propext ⟨const trivial, const (const trivial)⟩
@[smt_simp] theorem bool_impl_true2 {t : Prop} : (True → t) = t :=
  propext ⟨(· trivial), (const ·)⟩

@[smt_simp] theorem bool_or_true : (xs ∨ True ∨ ys) = True :=
  (true_or _).symm ▸ or_true _
@[smt_simp] theorem bool_or_false : (xs ∨ False ∨ ys) = (xs ∨ ys) :=
  (false_or _).symm ▸ rfl
@[smt_simp] theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ zs ∨ b ∨ ys) :=
  sorry
@[smt_simp] theorem bool_or_dup : (xs ∨ b ∨ ys ∨ b ∨ zs) = (xs ∨ b ∨ ys ∨ zs) :=
  sorry

@[smt_simp] theorem bool_and_true : (xs ∧ True ∧ ys) = (xs ∧ ys) := (true_and _).symm ▸ rfl
@[smt_simp] theorem bool_and_false : (xs ∧ False ∧ ys) = False := (false_and _).symm ▸ and_false _
@[smt_simp] theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ zs ∧ b ∧ ys) := sorry
@[smt_simp] theorem bool_and_dup : (xs ∧ b ∧ ys ∧ b ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := sorry

@[smt_simp] theorem bool_and_conf : (xs ∧ w ∧ ys ∧ ¬w ∧ zs) = False := sorry
@[smt_simp] theorem bool_or_taut : (xs ∨ w ∨ ys ∨ ¬w ∨ zs) = True := sorry

@[smt_simp] theorem ite_neg_branch [h : Decidable c] [Decidable y] : x = ¬y → ite c x y = (c = x) := fun hxny =>
  hxny ▸ h.byCases
    (fun hc => if_pos hc ▸ propext ⟨(propext ⟨const ·, const hc⟩), (· ▸ hc)⟩)
    (fun hnc => if_neg hnc ▸ propext
      ⟨fun hy => propext ⟨fun hc => False.elim (hnc hc), fun hny => False.elim (hny hy)⟩,
       fun hcny => bool_double_neg_elim (t := y) ▸ hcny ▸ hnc⟩)

end Smt.Reconstruction.Rewrites.Prop
