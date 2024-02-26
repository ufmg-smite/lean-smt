/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Std.Logic

namespace Classical

theorem epsilon_spec_aux' {α : Sort u} (h : Nonempty α) (p : α → Prop) : (¬∀ y, p y) → ¬p (@epsilon α h (fun x => ¬p x)) :=
  propext not_forall ▸ epsilon_spec_aux h (fun x => ¬p x)

end Classical

open Classical

namespace Smt.Reconstruct.Quant

universe u

theorem instForall {α : Sort u} (f : α → Prop) (a : α) :
  (forall a' : α, f a') → f a := λ h => h a

syntax "flipInstForall " term ("[" term "," term"]")? : term
macro_rules
| `(flipInstForall $premiss:term [$arg₁:term,  $arg₂:term]) =>
    `(instForall $arg₁ $arg₂ $premiss)

theorem instEqual₁ {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) → P t := λ h => h t rfl

theorem instEqual₂ {A : Type u} {P : A → Prop} {t : A} :
  P t → (forall x : A, x = t → P x) := by
  intros h x r
  rewrite [r]
  exact h

theorem instEqual {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) = P t := propext ⟨instEqual₁, instEqual₂⟩

theorem skolem₁ {α : Sort u} [i : Nonempty α] (p : α → Prop) : (∃ x, p x) → p (epsilon p) :=
  (strongIndefiniteDescription p i).property

theorem skolem₂ {α : Sort u} [Nonempty α] (p : α → Prop) : p (epsilon p) → ∃ x, p x := λ h =>
  ⟨epsilon p, h⟩

theorem smtSkolem {α : Sort u} [h: Nonempty α] (p : α → Prop) : (∃ x, p x) = p (epsilon p) :=
  propext ⟨@skolem₁ α h p, @skolem₂ α h p⟩

noncomputable def e₁ := epsilon (fun x : Int => ∃ y : Int, x + y > 0)
noncomputable def e₂ := epsilon (fun y : Int => e₁ + y > 0)

example : ∃ x₁ x₂ : Int, x₁ + x₂ > 0 = (e₁ + e₂ > 0) :=
  Eq.trans
    (smtSkolem (λ x₁ : Int => ∃ x₂, x₁ + x₂ > 0))
    (smtSkolem (λ x₂ : Int => e₁ + x₂ > 0))

example : (∀ x y : Int, x + y > 0) → (∀ y : Int, (3 : Int) + y > 0) := by
  intro h
  exact (instForall (fun x : Int => (forall y : Int, x + y > 0)) 3 h)

example : (∀ x y : Int, x + y > 0) → (3 : Int) + 4 > 0 := by
  intro h
  let s := (instForall (fun x : Int => (forall y : Int, x + y > 0)) 3 h)
  exact (instForall (fun (y : Int) => 3 + y > 0) 4 s)

example : (∀ x y : Int, x + y > 0) → (3 : Int) + 4 > 0 := by
  intro h
  let s1 := flipInstForall h [(fun x : Int => (forall y : Int, x + y > 0)), 3]
  let s2 := flipInstForall s1 [(fun (y : Int) => 3 + y > 0), 4]
  exact s2

end Smt.Reconstruct.Quant
