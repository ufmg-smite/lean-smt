/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, George Pîrlea
-/

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

/-- See `boolNeSimproc` for why we don't add this to the simp set directly. -/
theorem Bool.ne_eq_true {x y : Bool} : (x ≠ y) ↔ ((x : Prop) ≠ (y : Prop)) := by
  simp

attribute [embedding ↓] beq_iff_eq
attribute [embedding ↓] bne_iff_ne
attribute [embedding ↓] cond_eq_ite

@[embedding ↓]
theorem ite_eq_true [Decidable c] : (if c then t else e) = true ↔ if c then (t = true) else (e = true) := by
  simp only [Bool.ite_eq_true_distrib]

@[embedding ↓]
theorem cond_eq_true : (bif c then t else e) = true ↔ bif c then (t = true) else (e = true) := by
  simp only [Bool.cond_eq_true_distrib, Bool.cond_prop]

private theorem ite_congr' {α} [Decidable c₁] [Decidable c₂] {x₁ x₂ y₁ y₂ : α} (h₁ : c₁ = c₂) (h₂ : x₁ = x₂) (h₃ : y₁ = y₂) : ite c₁ x₁ y₁ = ite c₂ x₂ y₂ := by
  congr

open Lean in
@[match_pattern, expose] private def mkApp12 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : Expr) := mkApp8 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈

/--
`classical t` runs `t` in a scope where `Classical.propDecidable` is a low priority
local instance.
-/
private def Lean.Meta.withClassical [Monad m] [MonadEnv m] [MonadFinally m] [MonadLiftT MetaM m] (t : m α) :
    m α := do
  modifyEnv Meta.instanceExtension.pushScope
  Meta.addInstance ``Classical.propDecidable .local 100
  try
    t
  finally
    modifyEnv Meta.instanceExtension.popScope

namespace Smt.Preprocess.Embedding

open Lean Meta Simp in
simproc ↓ [embedding] IteCongrSimproc (ite _ _ _) := fun e => do
  let mkApp5 (.const ``ite [u]) α c hc t e := e | return .continue
  let cr ← simp c
  let ct ← simp t
  let ce ← simp e
  if cr.expr == c && ct.expr == t && ce.expr == e then return .continue
  let hc' ← if cr.expr == c then pure hc
            else Meta.withClassical (Meta.synthInstance (.app (.const ``Decidable []) cr.expr))
  let expr := mkApp5 (.const ``ite [u]) α cr.expr hc' ct.expr ce.expr
  let proof := mkApp12 (.const ``ite_congr' [u]) c cr.expr α hc hc' t ct.expr e ce.expr (← cr.getProof) (← ct.getProof) (← ce.getProof)
  return .done { expr, proof? := some proof }

open Lean Meta Simp in
/-- This is a `simproc` since `Bool.eq_eq_true` on its own can lead to simp
loops. This breaks if there are no occurrences of `decide` in the body of the
expression. -/
simproc ↓ [embedding] boolEqSimproc (_ = _) := fun e => do
  let_expr Eq α x y := e | return .continue
  if !(α.isConstOf ``Bool) then return .continue
  -- Prevent loops
  if y.isConstOf ``true then return .continue
  -- (x : Prop) is `x = true` by the Bool → Prop coercion
  let xAsProp ← mkEq x (mkConst ``true)
  let yAsProp ← mkEq y (mkConst ``true)
  let newExpr ← mkEq xAsProp yAsProp
  let iffPrf := mkApp2 (mkConst ``Bool.eq_eq_true) x y
  let proof ← mkAppM ``propext #[iffPrf]
  return .continue (some { expr := newExpr, proof? := some proof })

open Lean Meta Simp in
/-- This is a `simproc` rather than a plain simp lemma so we can skip the
`¬(b = true)` case. Without this guard, `Bool.ne_eq_true` would re-expand
the `¬(b = true)` produced by `Bool.not_eq_true''` into
`(b = true) ≠ (true = true)`, which then collapses to `(b = true) ≠ True`,
leaving spurious `≠ True` artifacts in the output. -/
simproc ↓ [embedding] boolNeSimproc (_ ≠ _) := fun e => do
  let_expr Ne α x y := e | return .continue
  if !(α.isConstOf ``Bool) then return .continue
  -- (x : Prop) is `x = true` by the Bool → Prop coercion
  let xAsProp ← mkEq x (mkConst ``true)
  let yAsProp ← mkEq y (mkConst ``true)
  let newExpr ← mkAppM ``Ne #[xAsProp, yAsProp]
  let iffPrf := mkApp2 (mkConst ``Bool.ne_eq_true) x y
  let proof ← mkAppM ``propext #[iffPrf]
  return .continue (some { expr := newExpr, proof? := some proof })

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
