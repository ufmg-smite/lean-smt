/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Archimedean
import Smt.Preprocess.Embedding.Attribute

@[embedding ↓]
theorem Real.ratCast_zero : ↑(0 : Rat) = (0 : Real) :=
  Rat.cast_zero

@[embedding ↓]
theorem Real.ratCast_one : ↑(1 : Rat) = (1 : Real) :=
  Rat.cast_one

@[embedding ↓]
theorem Real.ratCast_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : Rat) : Real) = (ofNat(n) : Real) :=
  Rat.cast_ofNat n

@[embedding ↓]
theorem Real.ratCast_neg (x : Rat) : ↑(-x) = (-(x : Real)) :=
  Rat.cast_neg x

@[embedding ↓]
theorem Real.ratCast_abs (x : Rat) : ↑|x| = |(x : Real)| :=
  Rat.cast_abs x

@[embedding ↓]
theorem Real.ratCast_floor (x : Rat) : ↑⌊x⌋ = ⌊(x : Real)⌋ :=
  (Rat.floor_cast x).symm

@[embedding ↓]
theorem Real.ratCast_ceil (x : Rat) : ↑⌈x⌉ = ⌈(x : Real)⌉ :=
  (Rat.ceil_cast x).symm

@[embedding ↓]
theorem Real.ratCast_add (x y : Rat) : ↑(x + y) = (x + y : Real) :=
  Rat.cast_add x y

@[embedding ↓]
theorem Real.ratCast_sub (x y : Rat) : ↑(x - y) = (x - y : Real) :=
  Rat.cast_sub x y

@[embedding ↓]
theorem Real.ratCast_mul (x y : Rat) : ↑(x * y) = (x * y : Real) :=
  Rat.cast_mul x y

@[embedding ↓]
theorem Real.ratCast_div (x y : Rat) : ↑(x / y) = (x / y : Real) :=
  Rat.cast_div x y

@[embedding ↓]
theorem Real.ratCast_inv (x : Rat) : ↑x⁻¹ = (x⁻¹ : Real) :=
  Rat.cast_inv x

@[embedding ↓]
theorem Real.ratCast_ite [Decidable c] {t e : Rat} :
    (if c then t else e : Rat) = (if c then t else e : Real) :=
  apply_ite Rat.cast c t e

@[embedding ↓ ←]
theorem Real.ratCast_eq {p q : Rat} : (p : Real) = q ↔ p = q :=
  Rat.cast_inj

@[embedding ↓ ←]
theorem Real.cast_ne {p q : Rat} : (p : Real) ≠ q ↔ p ≠ q := by
  simp only [ne_eq, Rat.cast_inj]

@[embedding ↓ ←]
theorem Real.cast_le {p q : Rat} : (p : Real) ≤ q ↔ p ≤ q :=
  Rat.cast_le

@[embedding ↓ ←]
theorem Real.cast_lt {p q : Rat} : (p : Real) < q ↔ p < q :=
  Rat.cast_lt

@[embedding ↓ ←]
theorem Real.cast_ge {p q : Rat} : (p : Real) ≥ q ↔ p ≥ q := by
  simp only [ge_iff_le, Rat.cast_le]

@[embedding ↓ ←]
theorem Real.cast_gt {p q : Rat} : (p : Real) > q ↔ p > q := by
  simp only [gt_iff_lt, Rat.cast_lt]

attribute [embedding ↓] Rat.cast_intCast

@[embedding ↓]
theorem Real.cast_intCast {n : Int} : (((n : Int) : Rat) : Real) = (n : Real) :=
  Rat.cast_intCast n

open Classical in
noncomputable def Real.toRat (x : Real) : Rat :=
  if h : ∃ a b : Int, x = a / b then
    let a := Exists.choose h
    let b := Exists.choose (Exists.choose_spec h)
    a / b
  else
    0

theorem Real.cast_exists_num_den (x : Rat) : ∃ a b : Int, (x : Real) = a / b := by
  exists x.num, x.den
  rewrite (occs := .pos [1]) [← Rat.num_div_den x]
  simp

theorem Real.toRat_eq {x : Rat} : Real.toRat x = x := by
  have h := Real.cast_exists_num_den x
  have hab : (x : Real) = Exists.choose h / Exists.choose (Exists.choose_spec h) :=
    Exists.choose_spec (Exists.choose_spec h)
  simp [Real.toRat, h, ← @Rat.cast_inj Real, Rat.cast_div, Rat.cast_intCast, ← hab]

@[embedding ↓]
theorem Real.cast_toRat {x : Real} (h : ∃ a b : Int, x = a / b) : (x.toRat : Real) = x := by
  have hab : x = Exists.choose h / Exists.choose (Exists.choose_spec h) :=
    Exists.choose_spec (Exists.choose_spec h)
  simp [Real.toRat, h, ← hab]

open Classical in
@[embedding ↓ low]
theorem Real.cast_toRat' {x : Real} : x.toRat = if ∃ a b : Int, x = a / b then x else 0 := by
  by_cases h : ∃ a b : Int, x = a / b
  · simp only [h, ↓reduceIte]
    rewrite (occs := .neg [1]) [h.choose_spec.choose_spec]
    simp [Real.toRat, h]
  · simp [Real.toRat, h]

@[embedding ↓]
theorem forall_rat_as_real {p : Rat → Prop} :
    (∀ x : Rat, p x) ↔ (∀ x : Real, (∃ a b : Int, x = a / b) → p x.toRat) := by
  constructor
  · intro h x hx
    apply h
  · intro h x
    have hx := h x (Real.cast_exists_num_den x)
    rewrite [Real.toRat_eq] at hx
    exact hx

-- This theorem is similar to the one below, but it does not have the implication in the
-- conclusion of the right-hand side, which (while redundant) helps the simplifier in
-- eliminating `Int.toNat` calls.
theorem exists_rat_as_real {p : Rat → Prop} :
    (∃ x : Rat, p x) ↔ (∃ x : Real, (∃ a b : Int, x = a / b) ∧ p x.toRat) := by
  constructor
  · intro ⟨x, hx⟩
    exists x
    constructor
    · exact Real.cast_exists_num_den x
    · rewrite [Real.toRat_eq]
      exact hx
  · intro ⟨x, hab, hx⟩
    exists x.toRat

@[embedding ↓]
theorem exists_rat_as_real' {p : Rat → Prop} :
    (∃ x : Rat, p x) ↔ (∃ x : Real, (∃ a b : Int, x = a / b) ∧ ((∃ a b : Int, x = a / b) → p x.toRat)) := by
  constructor
  · intro ⟨x, hx⟩
    exists x
    constructor
    · exact Real.cast_exists_num_den x
    · intro
      rewrite [Real.toRat_eq]
      exact hx
  · intro ⟨x, hab, hx⟩
    exists x.toRat
    exact hx hab

namespace Smt.Preprocess.Embedding

@[embedding ↓]
theorem forall_rat_in_as_real₁ {p : (Rat → α₁) → Prop} :
    (∀ f : Rat → α₁, p f) ↔ (∀ f : Real → α₁, p fun n => f n) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun x => f x.toRat
    simp only [Real.toRat_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_in_as_real₂ {p : (α₁ → Rat → α₂) → Prop} :
    (∀ f : α₁ → Rat → α₂, p f) ↔ (∀ f : α₁ → Real → α₂, p fun a₁ n => f a₁ n) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ x => f a₁ x.toRat
    simp only [Real.toRat_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_in_as_real₃ {p : (α₁ → α₂ → Rat → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Rat → α₃, p f) ↔ (∀ f : α₁ → α₂ → Real → α₃, p fun a₁ a₂ n => f a₁ a₂ n) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ x => f a₁ a₂ x.toRat
    simp only [Real.toRat_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_in_as_real₄ {p : (α₁ → α₂ → α₃ → Rat → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Rat → α₄, p f) ↔ (∀ f : α₁ → α₂ → α₃ → Real → α₄, p fun a₁ a₂ a₃ n => f a₁ a₂ a₃ n) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ x => f a₁ a₂ a₃ x.toRat
    simp only [Real.toRat_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_in_as_real₅ {p : (α₁ → α₂ → α₃ → α₄ → Rat → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Rat → α₅, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → Real → α₅, p fun a₁ a₂ a₃ a₄ n => f a₁ a₂ a₃ a₄ n) := by
  constructor
  · intro h f
    apply h
  · intro h f
    have hf := h fun a₁ a₂ a₃ a₄ x => f a₁ a₂ a₃ a₄ x.toRat
    simp only [Real.toRat_eq] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_out_as_real₁ {p : (α₁ → Rat) → Prop} :
    (∀ f : α₁ → Rat, p f) ↔ (∀ f : α₁ → Real, (∀ a₁, ∃ a b : Int, f a₁ = a / b) → p fun a₁ => (f a₁).toRat) := by
  constructor
  · intro h f hf
    apply h
  · intro h f
    have hf := h (fun a₁ => f a₁)
    simp only [Real.cast_exists_num_den, implies_true, Real.toRat_eq, forall_const] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_out_as_real₂ {p : (α₁ → α₂ → Rat) → Prop} :
    (∀ f : α₁ → α₂ → Rat, p f) ↔ (∀ f : α₁ → α₂ → Real, (∀ a₁ a₂, ∃ a b : Int, f a₁ a₂ = a / b) → p fun a₁ a₂ => (f a₁ a₂).toRat) := by
  constructor
  · intro h f hf
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ => f a₁ a₂)
    simp only [Real.cast_exists_num_den, implies_true, Real.toRat_eq, forall_const] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_out_as_real₃ {p : (α₁ → α₂ → α₃ → Rat) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Rat, p f) ↔ (∀ f : α₁ → α₂ → α₃ → Real, (∀ a₁ a₂ a₃, ∃ a b : Int, f a₁ a₂ a₃ = a / b) → p fun a₁ a₂ a₃ => (f a₁ a₂ a₃).toRat) := by
  constructor
  · intro h f hf
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => f a₁ a₂ a₃)
    simp only [Real.cast_exists_num_den, implies_true, Real.toRat_eq, forall_const] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_out_as_real₄ {p : (α₁ → α₂ → α₃ → α₄ → Rat) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Rat, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → Real, (∀ a₁ a₂ a₃ a₄, ∃ a b : Int, f a₁ a₂ a₃ a₄ = a / b) → p fun a₁ a₂ a₃ a₄ => (f a₁ a₂ a₃ a₄).toRat) := by
  constructor
  · intro h f hf
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄)
    simp only [Real.cast_exists_num_den, implies_true, Real.toRat_eq, forall_const] at hf
    exact hf

@[embedding ↓]
theorem forall_rat_out_as_real₅ {p : (α₁ → α₂ → α₃ → α₄ → Rat) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Rat, p f) ↔ (∀ f : α₁ → α₂ → α₃ → α₄ → Real, (∀ a₁ a₂ a₃ a₄, ∃ a b : Int, f a₁ a₂ a₃ a₄ = a / b) → p fun a₁ a₂ a₃ a₄ => (f a₁ a₂ a₃ a₄).toRat) := by
  constructor
  · intro h f hf
    apply h
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => f a₁ a₂ a₃ a₄)
    simp only [Real.cast_exists_num_den, implies_true, Real.toRat_eq, forall_const] at hf
    exact hf

open Lean Meta Simp

private def withNewLemmas (xs : Array Expr) (f : SimpM α) : SimpM α := do
  Simp.withFreshCache do
    let mut s ← Simp.getSimpTheorems
    let mut updated := false
    let ctx ← Simp.getContext
    for x in xs do
      if (← isProof x) then
        s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
        updated := true
    if updated then
      Simp.withSimpTheorems s f
    else
      f

def isFractional : Expr → Bool
  | .forallE _ _ b _ => isFractional b
  | mkApp2 (.const ``Exists [1]) (.const ``Int []) (.lam _ (.const ``Int []) (
    mkApp2 (.const ``Exists [1]) (.const ``Int []) (.lam _ (.const ``Int []) (
    mkApp3 (.const ``Eq [1]) (.const ``Real []) _ (mkApp6 (.const ``HDiv.hDiv [0, 0, 0]) ..)) _)) _) =>
    true
  | _ => false

def addRealIsFractionalLemma : Simproc := fun e => do
  let .forallE n p q bi := e | return .continue
  if !isFractional p then return .continue
  let rp ← simp p
  let r ← Meta.withLocalDeclD n rp.expr fun hp => do
    let rq ← withNewLemmas #[hp] (simp q)
    match rq.proof? with
    | none    => mkImpCongr e rp rq
    | some hq =>
      let hq ← mkLambdaFVars #[hp] hq
      return { expr := .forallE n rp.expr rq.expr bi, proof? := ← mkImpCongrCtx (← rp.getProof) hq }
  return .done r

simproc ↓ [embedding] add_real_is_fractional_lemma (_ → _) :=
  addRealIsFractionalLemma

end Smt.Preprocess.Embedding
