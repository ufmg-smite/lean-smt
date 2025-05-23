/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Prop.Core

namespace Smt.Reconstruct.Prop

-- https://github.com/cvc5/cvc5/blob/main/src/theory/booleans/rewrites

open Function

theorem bool_double_not_elim : (¬¬t) = t :=
  propext Classical.not_not
theorem bool_not_true (h : t = False) : (¬t) = True := h ▸ propext not_false_iff
theorem bool_not_false (h : t = True) : (¬t) = False := h ▸ propext not_true

theorem bool_eq_true : (t = True) = t :=
  propext ⟨of_eq_true, eq_true⟩
theorem bool_eq_false : (t = False) = ¬t :=
  propext ⟨(· ▸ not_false), eq_false⟩
theorem bool_eq_nrefl : (t = ¬t) = False :=
  propext ⟨(have H : t ↔ ¬t := · ▸ ⟨id, id⟩; have f h := H.mp h h; f (H.mpr f)), False.elim⟩

theorem bool_impl_false1 : (t → False) = ¬t :=
  propext ⟨(·), (·)⟩
theorem bool_impl_false2 : (False → t) = True :=
  propext ⟨const _ trivial, const _ False.elim⟩
theorem bool_impl_true1 {t : Prop} : (t → True) = True :=
  propext ⟨const _ trivial, const _ (const _ trivial)⟩
theorem bool_impl_true2 {t : Prop} : (True → t) = t :=
  propext ⟨(· trivial), const _⟩
theorem bool_impl_elim : (t → s) = orN [¬t, s] :=
  propext ⟨fun hts => (Classical.em t).elim (Or.inr $ hts ·) Or.inl, (fun ht => ·.elim (absurd ht) id)⟩

-- used in proof elaboration
theorem bool_dual_impl_eq : andN [t → s, s → t] = (t = s) :=
  propext ⟨fun ⟨hts, hst⟩ => propext ⟨hts, hst⟩, (· ▸ ⟨id, id⟩)⟩

theorem bool_and_conf : andN (xs ++ w :: (ys ++ (¬w) :: zs)) = False := by
  simp only [andN_append, andN_cons_append]
  exact propext ⟨fun ⟨_, hw, _, hnw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_and_conf2 : andN (xs ++ (¬w) :: (ys ++ w :: zs)) = False := by
  simp only [andN_append, andN_cons_append]
  exact propext ⟨fun ⟨_, hnw, _, hw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_or_taut : orN (xs ++ w :: (ys ++ (¬w) :: zs)) = True := by
  simp only [orN_append, orN_cons_append]
  exact propext $ .intro
    (const _ trivial)
    (eq_true (Classical.em w) ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))
theorem bool_or_taut2 : orN (xs ++ (¬w) :: (ys ++ w :: zs)) = True := by
  simp only [orN_append, orN_cons_append]
  exact propext $ .intro
    (const _ trivial)
    (eq_true (Classical.em w).symm ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))

theorem bool_or_de_morgan : (¬orN (x :: y :: zs)) = andN [¬x, ¬orN (y :: zs)] :=
  propext not_or
theorem bool_implies_de_morgan : (¬(x → y)) = andN [x, ¬y] :=
  propext Classical.not_imp_iff_and_not
theorem bool_and_de_morgan : (¬andN (x :: y :: zs)) = orN [¬x, ¬andN (y :: zs)] :=
  propext Classical.not_and_iff_not_or_not

theorem bool_or_and_distrib :
  orN (andN (y₁ :: y₂ :: ys) :: z₁ :: zs) = andN [orN (y₁ :: z₁ :: zs), orN (andN (y₂ :: ys) :: z₁ :: zs)] :=
  match zs with
  | []
  | _ :: _ => propext and_or_right

-- Used for diamonds preprocessing
theorem bool_implies_or_distrib : (orN (y₁ :: y₂ :: ys) → z) = andN [y₁ → z, orN (y₂ :: ys) → z] :=
  match ys with
  | []
  | _ :: _ => propext or_imp

theorem bool_xor_refl : XOr x x = False :=
  propext ⟨(·.elim absurd (flip absurd)), False.elim⟩
theorem bool_xor_nrefl : (XOr x ¬x) = True :=
  propext ⟨const _ trivial,
           const _ ((Classical.em x).elim (fun hx => .inl hx (· hx)) (fun hnx => .inr hnx hnx))⟩
theorem bool_xor_false : XOr x False = x :=
  propext ⟨(·.elim (flip (const _ id)) (const _ False.elim)), (.inl · not_false)⟩
theorem bool_xor_true : XOr x True = ¬x :=
  propext ⟨(·.elim (const _ (False.elim $ not_true.mp ·)) (flip (const _ id))), (.inr · trivial)⟩
theorem bool_xor_comm : XOr x y = XOr y x :=
  propext ⟨XOr.symm, XOr.symm⟩
theorem bool_xor_elim : (XOr x y) = ((¬x) = y) :=
  propext (Iff.intro
    (·.elim (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩) (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (fun hnxy => (Classical.em y).elim (fun hy => XOr.inr (hnxy ▸ hy) hy)
                                       (fun hny => XOr.inl (Classical.not_not.mp (hnxy ▸ hny)) hny)))
theorem bool_not_xor_elim : (¬XOr x y) = (x = y) :=
  propext (Iff.intro
    (fun hnxy => propext (Iff.intro
       (fun hx => Classical.byContradiction (hnxy $ XOr.inl hx ·))
       (fun hy => Classical.byContradiction (hnxy $ XOr.inr · hy))))
    fun hxy => hxy ▸ fun hxx => hxx.elim (fun hx hnx => hnx hx) (· ·))

theorem bool_not_eq_elim1 : (¬x = y) = ((¬x) = y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩)
      (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (@iff_not_self x $ · ▸ · ▸ Iff.rfl))
theorem bool_not_eq_elim2 : (¬x = y) = (x = ¬y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨const _ hny, const _ hx⟩)
      (fun hnx hy => propext ⟨(absurd · hnx), (absurd hy ·)⟩))
    (@iff_not_self y $ · ▸ · ▸ Iff.rfl))

theorem ite_neg_branch [h : Decidable c] : x = ¬y → ite c x y = (c = x) :=
  fun hxny => hxny ▸ h.byCases
    (fun hc => if_pos hc ▸ propext ⟨(propext ⟨const _ ·, const _ hc⟩), (· ▸ hc)⟩)
    (fun hnc => if_neg hnc ▸ propext
      ⟨fun hy => propext ⟨fun hc => False.elim (hnc hc), fun hny => False.elim (hny hy)⟩,
       fun hcny => bool_double_not_elim (t := y) ▸ hcny ▸ hnc⟩)

theorem ite_then_true [h : Decidable c] : ite c True x = orN [c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨const _ (Or.inl hc), const _ trivial⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨Or.inr, (·.elim (absurd · hnc) id)⟩)
theorem ite_else_false [h : Decidable c] : ite c x False = andN [c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨And.intro hc, And.right⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨False.elim, (absurd ·.left hnc)⟩)
theorem ite_then_false [h : Decidable c] : ite c False x = andN [¬c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨False.elim, (absurd hc ·.left)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨And.intro hnc, And.right⟩)
theorem ite_else_true [h : Decidable c] : ite c x True = orN [¬c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨Or.inr, (·.elim (absurd hc) id)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨const _ (Or.inl hnc), const _ trivial⟩)

theorem ite_then_lookahead_self [h : Decidable c] : ite c c x = ite c True x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_true hc)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_self [h : Decidable c] : ite c x c = ite c x False := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_false hnc)

theorem ite_then_lookahead_not_self [h : Decidable c] : ite c (¬c) x = ite c False x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_false (not_not_intro hc))
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_not_self [h : Decidable c] : ite c x (¬c) = ite c x True := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_true hnc)

theorem ite_expand [h : Decidable c] : ite c x y = andN [orN [¬c, x], orN [c, y]] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨(⟨Or.inr ·, Or.inl hc⟩), (·.left.resolve_left (not_not_intro hc))⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨(⟨Or.inl hnc, Or.inr ·⟩), (·.right.resolve_left hnc)⟩)

theorem bool_not_ite_elim [h : Decidable c] : (¬ite c x y) = ite c (¬x) (¬y) := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)

end Smt.Reconstruct.Prop
