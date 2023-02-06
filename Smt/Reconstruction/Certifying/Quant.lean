open Classical

universe u

theorem instForall {α : Sort u} (f : α → Prop) (a : α) :
  (forall a' : α, f a') → f a := λ h => h a

syntax "flipInstForall " (term)? (term)? (term)? : term
macro_rules
| `(flipInstForall $premiss:term $arg₁:term $arg₂:term) =>
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

example : (∀ x y : Int, x + y > 0) → (3 : Int) + 4 > 0 := by
  intro h
  let s := (instForall (fun x : Int => (forall y : Int, x + y > 0)) 3 h)
  exact (instForall (fun y : Int => 3 + y > 0) 4 s)
