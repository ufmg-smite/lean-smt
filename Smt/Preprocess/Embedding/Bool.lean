import Smt.Preprocess.Embedding.Attribute
import Smt.Reconstruct.Prop.Core

@[embedding ↓]
theorem Bool.true_eq_true : (true = true) ↔ True :=
  eq_self_iff_true true

attribute [embedding ↓] Bool.false_eq_true
attribute [embedding ↓] decide_eq_true_iff

@[embedding ↓]
theorem Bool.not_eq_true'' {x : Bool} : (!x : Bool) ↔ ¬(x : Prop) := by
  cases x <;> decide

attribute [embedding ↓] Bool.and_eq_true
attribute [embedding ↓] Bool.or_eq_true

@[embedding ↓]
theorem Bool.xor_eq_true {x y : Bool} : (x ^^ y : Bool) ↔ (XOr (x : Prop) (y : Prop)) := by
  cases x <;> cases y <;> decide

@[embedding ↓ low]
theorem Bool.eq_eq_true {x y : Bool} : (x = y) ↔ ((x : Prop) = (y : Prop)) := by
  simp

@[embedding ↓ low]
theorem Bool.ne_eq_true {x y : Bool} : (x ≠ y) ↔ ((x : Prop) ≠ (y : Prop)) := by
  simp

attribute [embedding ↓] beq_iff_eq
attribute [embedding ↓] bne_iff_ne
attribute [embedding ↓] cond_eq_if

namespace Smt.Preprocess.Embedding

open Classical

@[embedding ↓]
theorem forall_bool_as_prop {p : Bool → Prop} :
    (∀ x : Bool, p x) ↔ (∀ x : Prop, p (decide x)) := by
  constructor
  · intro h x
    exact h x
  · intro h x
    have hx := h x
    rewrite [@Bool.decide_eq_true] at hx
    exact hx

@[embedding ↓]
theorem exists_bool_as_prop {p : Bool → Prop} :
    (∃ x : Bool, p x) ↔ (∃ x : Prop, p (decide x)) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exists x
    rewrite [@Bool.decide_eq_true]
    exact hx
  · intro h
    obtain ⟨x, hx⟩ := h
    exists (decide x)

@[embedding ↓]
theorem forall_bool_in_as_prop₁ {p : (Bool → α₁) → Prop} :
    (∀ f : Bool → α₁, p f) ↔ (∀ f : Prop → α₁, p fun b => f b) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun x => f x
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_in_as_prop₂ {p : (α₁ → Bool → α₂) → Prop} :
    (∀ f : α₁ → Bool → α₂, p f) ↔ (∀ f : α₁ → Prop → α₂, p fun a₁ b => f a₁ b) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ x => f a₁ x
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_in_as_prop₃ {p : (α₁ → α₂ → Bool → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Bool → α₃, p f) ↔ (∀ f : α₁ → α₂ → Prop → α₃, p fun a₁ a₂ b => f a₁ a₂ b) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ x => f a₁ a₂ x
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_in_as_prop₄ {p : (α₁ → α₂ → α₃ → Bool → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Bool → α₄, p f) ↔ (∀ f : α₁ → α₂ → α₃ → Prop → α₄, p fun a₁ a₂ a₃ b => f a₁ a₂ a₃ b) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ x => f a₁ a₂ a₃ x
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_in_as_prop₅ {p : (α₁ → α₂ → α₃ → α₄ → Bool → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool → α₅, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → Prop → α₅, p fun a₁ a₂ a₃ a₄ b => f a₁ a₂ a₃ a₄ b) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ x
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_out_as_prop₁ {p : (α₁ → Bool) → Prop} :
    (∀ f : α₁ → Bool, p f) ↔ (∀ f : α₁ → Prop, p (fun a₁ => f a₁)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h (fun a₁ => f a₁)
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_out_as_prop₂ {p : (α₁ → α₂ → Bool) → Prop} :
    (∀ f : α₁ → α₂ → Bool, p f) ↔ (∀ f : α₁ → α₂ → Prop, p (fun a₁ a₂ => f a₁ a₂)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ => f a₁ a₂)
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_out_as_prop₃ {p : (α₁ → α₂ → α₃ → Bool) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Bool, p f) ↔ (∀ f : α₁ → α₂ → α₃ → Prop, p (fun a₁ a₂ a₃ => f a₁ a₂ a₃)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => f a₁ a₂ a₃)
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_out_as_prop₄ {p : (α₁ → α₂ → α₃ → α₄ → Bool) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Bool, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → Prop, p (fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄)
    simp only [@Bool.decide_eq_true] at hf
    exact hf

@[embedding ↓]
theorem forall_bool_out_as_prop₅ {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Bool) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Bool, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop, p (fun a₁ a₂ a₃ a₄ a₅ => f a₁ a₂ a₃ a₄ a₅)) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ a₅ => f a₁ a₂ a₃ a₄ a₅)
    simp only [@Bool.decide_eq_true] at hf
    exact hf

end Smt.Preprocess.Embedding
