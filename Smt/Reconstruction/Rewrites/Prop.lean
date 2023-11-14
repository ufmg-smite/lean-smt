/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruction.Rewrites.Simp
import Std.Logic

namespace Smt.Reconstruction.Rewrites.«Prop»

-- https://github.com/cvc5/cvc5/blob/proof-new/src/theory/booleans/rewrites

open Function

@[smt_simp] theorem bool_double_not_elim [Decidable t] : (¬¬t) = t :=
  propext ⟨Decidable.of_not_not, not_not_intro⟩

@[smt_simp] theorem bool_eq_true : (t = True) = t :=
  propext ⟨of_eq_true, eq_true⟩
@[smt_simp] theorem bool_eq_false : (t = False) = (Not t) :=
  propext ⟨(· ▸ not_false), eq_false⟩
@[smt_simp] theorem bool_eq_nrefl : (t = ¬t) = False :=
  propext ⟨(have H : t ↔ ¬t := · ▸ ⟨id, id⟩; have f h := H.mp h h; f (H.mpr f)), False.elim⟩

@[smt_simp] theorem bool_impl_false1 : (t → False) = ¬t :=
  propext ⟨(·), (·)⟩
@[smt_simp] theorem bool_impl_false2 : (False → t) = True :=
  propext ⟨const _ trivial, const _ False.elim⟩
@[smt_simp] theorem bool_impl_true1 : (t → True) = True :=
  propext ⟨const _ trivial, const _ (const _ trivial)⟩
@[smt_simp] theorem bool_impl_true2 {t : Prop} : (True → t) = t :=
  propext ⟨(· trivial), const _⟩
@[smt_simp] theorem bool_impl_elim [h : Decidable t] : (t → s) = (¬t ∨ s) :=
  propext ⟨fun hts => h.byCases (Or.inr $ hts ·) Or.inl, (fun ht => ·.elim (absurd ht) id)⟩

@[smt_simp] theorem bool_or_true : (xs ∨ True ∨ ys) = True :=
  (true_or _).symm ▸ or_true _
@[smt_simp] theorem bool_or_false : (xs ∨ False ∨ ys) = (xs ∨ ys) :=
  (false_or _).symm ▸ rfl
@[smt_simp] theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ zs ∨ b ∨ ys) :=
  propext (@Or.comm b ys) ▸ propext (@Or.comm _ zs) ▸ rfl
@[smt_simp] theorem bool_or_dup : (xs ∨ b ∨ ys ∨ b ∨ zs) = (xs ∨ b ∨ ys ∨ zs) :=
  propext (@or_assoc ys b zs) ▸ propext (@Or.comm ys b) ▸ propext (@or_assoc b _ zs) ▸
  propext (@or_assoc b b ys) ▸ or_self _ ▸ propext (@or_assoc b ys zs) ▸ rfl

@[smt_simp] theorem bool_and_true : (xs ∧ True ∧ ys) = (xs ∧ ys) :=
  (true_and _).symm ▸ rfl
@[smt_simp] theorem bool_and_false : (xs ∧ False ∧ ys) = False :=
  (false_and _).symm ▸ and_false _
@[smt_simp] theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ zs ∧ b ∧ ys) :=
  propext (@And.comm b ys) ▸ propext (@And.comm _ zs) ▸ rfl
@[smt_simp] theorem bool_and_dup : (xs ∧ b ∧ ys ∧ b ∧ zs) = (xs ∧ b ∧ ys ∧ zs) :=
  propext (@and_assoc ys b zs) ▸ propext (@And.comm ys b) ▸ propext (@and_assoc b _ zs) ▸
  propext (@and_assoc b b ys) ▸ and_self _ ▸ propext (@and_assoc b ys zs) ▸ rfl

@[smt_simp] theorem bool_and_conf : (xs ∧ w ∧ ys ∧ ¬w ∧ zs) = False :=
  propext ⟨fun ⟨_, hw, _, hnw, _⟩ => absurd hw hnw, False.elim⟩
@[smt_simp] theorem bool_or_taut [h : Decidable w] : (xs ∨ w ∨ ys ∨ ¬w ∨ zs) = True := propext $ .intro
  (const _ trivial)
  (eq_true h.em ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))

@[smt_simp] theorem bool_xor_refl : (x ≠ x) = False :=
  propext ⟨(nomatch ·), False.elim⟩
@[smt_simp] theorem bool_xor_nrefl : (x ≠ ¬x) = True :=
  propext ⟨const _ trivial, const _ (show x = ¬x → False from bool_eq_nrefl ▸ id)⟩
@[smt_simp] theorem bool_xor_false [h : Decidable x] : (x ≠ False) = x :=
  propext ⟨(h.of_not_not $ @bool_eq_false x ▸ ·), flip (· ▸ ·)⟩
@[smt_simp] theorem bool_xor_true : (x ≠ True) = ¬x :=
  propext ⟨(· $ propext ⟨const _ trivial, const _ ·⟩), ne_true_of_not⟩
@[smt_simp] theorem bool_xor_comm : (x ≠ y) = (y ≠ x) :=
  propext ⟨Ne.symm, Ne.symm⟩
@[smt_simp] theorem bool_xor_elim : (x ≠ y) = ¬(x = y) := rfl

@[smt_simp] theorem ite_neg_branch [h : Decidable c] [Decidable y] : x = ¬y → ite c x y = (c = x) :=
  fun hxny => hxny ▸ h.byCases
    (fun hc => if_pos hc ▸ propext ⟨(propext ⟨const _ ·, const _ hc⟩), (· ▸ hc)⟩)
    (fun hnc => if_neg hnc ▸ propext
      ⟨fun hy => propext ⟨fun hc => False.elim (hnc hc), fun hny => False.elim (hny hy)⟩,
       fun hcny => bool_double_not_elim (t := y) ▸ hcny ▸ hnc⟩)

@[smt_simp] theorem ite_then_true [h : Decidable c] : ite c True x = (c ∨ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨const _ (Or.inl hc), const _ trivial⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨Or.inr, (·.elim (absurd · hnc) id)⟩)
@[smt_simp] theorem ite_else_false [h : Decidable c] : ite c x False = (c ∧ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨And.intro hc, And.right⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨False.elim, (absurd ·.left hnc)⟩)
@[smt_simp] theorem ite_then_false [h : Decidable c] : ite c False x = (¬c ∧ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨False.elim, (absurd hc ·.left)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨And.intro hnc, And.right⟩)
@[smt_simp] theorem ite_else_true [h : Decidable c] : ite c x True = (¬c ∨ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨Or.inr, (·.elim (absurd hc) id)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨const _ (Or.inl hnc), const _ trivial⟩)

@[smt_simp] theorem ite_then_lookahead_self [h : Decidable c] : ite c c x = ite c True x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_true hc)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
@[smt_simp] theorem ite_else_lookahead_self [h : Decidable c] : ite c x c = ite c x False := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_false hnc)

end Smt.Reconstruction.Rewrites.«Prop»
