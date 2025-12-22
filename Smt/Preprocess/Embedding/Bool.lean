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

/-- See `boolEqSimproc` for why we don't add this to the simp set directly. -/
theorem Bool.eq_eq_true {x y : Bool} : (x = y) ↔ ((x : Prop) = (y : Prop)) := by
  simp

@[embedding ↓ low]
theorem Bool.ne_eq_true {x y : Bool} : (x ≠ y) ↔ ((x : Prop) ≠ (y : Prop)) := by
  simp

attribute [embedding ↓] beq_iff_eq
attribute [embedding ↓] bne_iff_ne
attribute [embedding ↓] cond_eq_if

namespace Smt.Preprocess.Embedding

@[embedding ↓ low]
theorem Bool.decide_eq_bool {p : Prop} [Decidable p] {b : Bool} : (decide p = b) ↔ (p ↔ (b : Prop)) := by
  cases b <;> simp

@[embedding ↓ low]
theorem Bool.bool_eq_decide {p : Prop} [Decidable p] {b : Bool} : (b = decide p) ↔ ((b : Prop) ↔ p) := by
  cases b <;> simp

open Lean Meta Simp in
/-- This is a `simproc` since `Bool.eq_eq_true` on its own can lead to simp
loops. This breaks if there are no occurrences of `decide` in the body of the
expression. -/
simproc ↓ [embedding] boolEqSimproc (_ = _) := fun e => do
  let_expr Eq α x y := e | return .continue
  unless α.isConstOf ``Bool do return .continue
  if !(mkConst ``decide).occurs e then
    return .done { expr := e, proof? := none }
  -- (x : Prop) is `x = true` by the Bool → Prop coercion
  let xAsProp ← mkEq x (mkConst ``true)
  let yAsProp ← mkEq y (mkConst ``true)
  let newExpr ← mkEq xAsProp yAsProp
  let iffPrf := mkApp2 (mkConst ``Bool.eq_eq_true) x y
  let proof ← mkAppM ``propext #[iffPrf]
  return .done { expr := newExpr, proof? := some proof }

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

attribute [embedding ↓ low] decide_implies decide_ite ite_then_decide_self
ite_else_decide_self ite_then_decide_not_self ite_else_decide_not_self
dite_eq_left_iff dite_eq_right_iff left_eq_dite_iff right_eq_dite_iff
dite_iff_left_iff dite_iff_right_iff left_iff_dite_iff right_iff_dite_iff
ite_eq_left_iff ite_eq_right_iff left_eq_ite_iff right_eq_ite_iff
ite_iff_left_iff ite_iff_right_iff left_iff_ite_iff right_iff_ite_iff
dite_then_false dite_else_false dite_then_true dite_else_true

@[embedding ↓ low]
theorem Bool.bool_eq_ite_iff {p : Prop} [Decidable p] {b x y : Bool} :
    (b = ite p x y) ↔ (if p then (b : Prop) ↔ (x : Prop) else (b : Prop) ↔ (y : Prop)) := by
  by_cases hp : p <;> simp_all

@[embedding ↓ low]
theorem Bool.ite_eq_bool_iff {p : Prop} [Decidable p] {b x y : Bool} :
    (ite p x y = b) ↔ (if p then (x : Prop) ↔ (b : Prop) else (y : Prop) ↔ (b : Prop)) := by
  by_cases hp : p <;> simp_all

end Smt.Preprocess.Embedding
