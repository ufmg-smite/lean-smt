/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruct.Util

theorem exists_congr_eq {p q : α → Prop} (h : ∀ a, p a = q a) : (∃ a, p a) = (∃ a, q a) :=
  propext (exists_congr (h · ▸ Iff.rfl))

theorem forall_const_eq (α : Sort u) [Nonempty α] {p q : Prop} (h : p = q) : (α → p) = q :=
  h ▸ propext (forall_const α)

namespace Classical

theorem exists_elim {α} {p : α → Prop} : (∃ x, p x) = ¬∀ x, ¬p x :=
  Eq.symm (propext not_forall_not)

theorem not_forall_eq (p : α → Prop) : (¬∀ (x : α), p x) = ∃ x, ¬p x := propext not_forall

theorem not_not_eq (p : Prop) : (¬¬p) = p := propext not_not

theorem epsilon_spec_aux' {α : Sort u} (h : Nonempty α) (p : α → Prop) : (¬∀ y, p y) → ¬p (@epsilon α h (fun x => ¬p x)) :=
  propext not_forall ▸ epsilon_spec_aux h (fun x => ¬p x)

end Classical

namespace Smt.Reconstruct.Quant

theorem miniscope_and {p q : α → Prop} : (∀ x, p x ∧ q x) = ((∀ x, p x) ∧ (∀ x, q x)) :=
  propext forall_and

theorem miniscope_andN {α : Type u} {ps : List (α → Prop)} : (∀ x, andN (ps.map (· x))) = andN (ps.map (∀ x, · x)) :=
  match ps with
  | []             => by simp [andN]
  | [_]            => rfl
  | p₁ :: p₂ :: ps => miniscope_and ▸ @miniscope_andN α (p₂ :: ps) ▸ rfl

theorem miniscope_or_left {p : α → Prop} {q : Prop} : (∀ x, p x ∨ q) = ((∀ x, p x) ∨ q) :=
  propext <| Iff.intro
    (fun hpxq => (Classical.em q).elim (Or.inr ·) (fun hnq => Or.inl (fun x => (hpxq x).resolve_right hnq)))
    (fun hpxq x => hpxq.elim (fun hpx => Or.inl (hpx x)) (Or.inr ·))

theorem miniscope_or_right {p : Prop} {q : α → Prop} : (∀ x, p ∨ q x) = (p ∨ (∀ x, q x)) :=
  propext or_comm ▸ miniscope_or_left ▸ forall_congr (fun _ => propext or_comm)

theorem miniscope_orN {ps : List Prop} {q : α → Prop} {rs : List Prop} : (∀ x, orN (ps ++ q x :: rs)) = orN (ps ++ (∀ x, q x) :: rs) :=
  match ps with
  | []             => by cases rs <;> simp [orN, miniscope_or_left]
  | [p]            => miniscope_or_right ▸ @miniscope_orN α [] q rs ▸ rfl
  | p₁ :: p₂ :: ps => miniscope_or_right ▸ @miniscope_orN α (p₂ :: ps) q rs ▸ rfl

theorem var_elim_eq {t : α} : (∀ x, x ≠ t) = False :=
  propext ⟨fun hnxt => absurd rfl (hnxt t), False.elim⟩

theorem var_elim_eq_or {t : α} {p : α → Prop} : (∀ x, x ≠ t ∨ p x) = p t :=
  propext <| Iff.intro
    (fun hpx => (hpx t).resolve_left (absurd rfl ·))
    (fun hpt x => (Classical.em (x = t)).elim (Or.inr $ · ▸ hpt) (Or.inl ·))

end Smt.Reconstruct.Quant
