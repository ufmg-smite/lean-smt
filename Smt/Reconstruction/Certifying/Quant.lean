open Classical

universe u

theorem instForAll {α : Sort u} {f : α → Prop} {a : α} :
  (forall a' : α, f a') → f a := λ h => h a

theorem instEqual₁ {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) → P t := λ h => h t rfl

theorem instEqual₂ {A : Type u} {P : A → Prop} {t : A} :
  P t → (forall x : A, x = t → P x) := by
  intros h x r
  rewrite [r]
  exact h

theorem instEqual {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) ↔ P t := ⟨instEqual₁, instEqual₂⟩

theorem skolem₁ {α : Sort u} [i : Nonempty α] (p : α → Prop) : (∃ x, p x) → p (epsilon p) :=
  (strongIndefiniteDescription p i).property

theorem skolem₂ {α : Sort u} [Nonempty α] (p : α → Prop) : p (epsilon p) → ∃ x, p x := λ h =>
  ⟨epsilon p, h⟩

theorem smtSkolem {α : Sort u} [h: Nonempty α] (p : α → Prop) : (∃ x, p x) ↔ p (epsilon p) :=
  ⟨@skolem₁ α h p, @skolem₂ α h p⟩

def f: Prop := ∃ _: Nat, True
axiom g : f

#check Iff.mp (smtSkolem (λ _ => True)) g

