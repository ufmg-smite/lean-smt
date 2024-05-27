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

end Smt.Reconstruct.Quant
