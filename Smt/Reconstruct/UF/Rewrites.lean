/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt.Reconstruct.UF

-- https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites

variable {t s r : α}

-- Equality

theorem eq_refl : (t = t) = True := eq_self t
theorem eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩

theorem eq_cond_deq (h : (s = r) = False) : ((t = s) = (t = r)) = (¬t = s ∧ ¬t = r) :=
  propext <| Iff.intro
    (fun hsr => And.intro (fun hts => absurd (hts ▸ hsr ▸ hts) (of_eq_false h))
                          (fun htr => absurd (htr ▸ Eq.symm (hsr ▸ htr)) (of_eq_false h)))
    (fun hnsr => propext ⟨(absurd · hnsr.left), (absurd · hnsr.right)⟩)

theorem distinct_binary_elim : (t ≠ s) = ¬(t = s) := rfl

end Smt.Reconstruct.UF
