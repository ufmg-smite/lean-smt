/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/

import Smt.Preprocess.Embedding.Attribute

attribute [embedding ↓] Fin.ext_iff
attribute [embedding ↓] Fin.val_zero
attribute [embedding ↓] Fin.val_one
attribute [embedding ↓] Fin.val_ofNat
attribute [embedding ↓] Fin.mk.injEq

namespace Smt.Preprocess.Embedding

def ofIntFin (n : Nat) (x : Int) (h : 0 ≤ x ∧ x < n) : Fin n :=
  ⟨x.toNat, (Int.toNat_lt h.1).2 h.2⟩

@[embedding ↓]
theorem Int.natCast_ofIntFin {n : Nat} {x : Int} {h : 0 ≤ x ∧ x < n} :
    (((ofIntFin n x h : Fin n) : Nat) : Int) = x :=
  Int.toNat_of_nonneg h.1

theorem ofIntFin_of_fin {n : Nat} (x : Fin n)
    (h : 0 ≤ ((x : Nat) : Int) ∧ ((x : Nat) : Int) < n) :
    ofIntFin n ((x : Nat) : Int) h = x := by
  apply Fin.ext
  simp [ofIntFin]

def ofIntFinTotal (n : Nat) [NeZero n] (x : Int) : Fin n :=
  Fin.ofNat n x.toNat

theorem ofIntFinTotal_of_fin {n : Nat} [NeZero n] (x : Fin n) :
    ofIntFinTotal n ((x : Nat) : Int) = x := by
  apply Fin.ext
  simp [ofIntFinTotal]

@[embedding ↓]
theorem forall_fin_as_int {n : Nat} {p : Fin n → Prop} :
    (∀ x : Fin n, p x) ↔
    (∀ x : Int, (h : 0 ≤ x ∧ x < n) → p (ofIntFin n x h)) := by
  constructor
  · intro h x hx
    exact h (ofIntFin n x hx)
  · intro h x
    have hx := h ((x : Nat) : Int) (by
      constructor
      · exact Int.natCast_nonneg x.val
      · exact_mod_cast x.isLt)
    simpa [ofIntFin_of_fin] using hx

@[embedding ↓]
theorem exists_fin_as_int {n : Nat} {p : Fin n → Prop} :
    (∃ x : Fin n, p x) ↔
    (∃ x : Int, ∃ h : 0 ≤ x ∧ x < n, p (ofIntFin n x h)) := by
  constructor
  · intro ⟨x, hx⟩
    refine ⟨(x : Nat), ?_, ?_⟩
    · constructor
      · exact Int.natCast_nonneg x.val
      · exact_mod_cast x.isLt
    · simpa [ofIntFin_of_fin] using hx
  · intro ⟨x, hx, hp⟩
    exact ⟨ofIntFin n x hx, hp⟩

@[embedding ↓]
theorem forall_fin_out_as_int₁ {n : Nat} {p : (α₁ → Fin n) → Prop} :
    (∀ f : α₁ → Fin n, p f) ↔
    (∀ f : α₁ → Int, (hf : ∀ a₁, 0 ≤ f a₁ ∧ f a₁ < n) →
      p (fun a₁ => ofIntFin n (f a₁) (hf a₁))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ => ofIntFin n (f a₁) (hf a₁))
  · intro h f
    have hf := h (fun a₁ => ((f a₁ : Nat) : Int)) (fun a₁ => by
      constructor
      · exact Int.natCast_nonneg (f a₁).val
      · exact Int.ofNat_lt.mpr (f a₁).isLt)
    simpa [ofIntFin_of_fin] using hf

@[embedding ↓]
theorem forall_fin_out_as_int₂ {n : Nat} {p : (α₁ → α₂ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → Int, (hf : ∀ a₁ a₂, 0 ≤ f a₁ a₂ ∧ f a₁ a₂ < n) →
      p (fun a₁ a₂ => ofIntFin n (f a₁ a₂) (hf a₁ a₂))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ => ofIntFin n (f a₁ a₂) (hf a₁ a₂))
  · intro h f
    have hf := h (fun a₁ a₂ => ((f a₁ a₂ : Nat) : Int)) (fun a₁ a₂ => by
      constructor
      · exact Int.natCast_nonneg (f a₁ a₂).val
      · exact Int.ofNat_lt.mpr (f a₁ a₂).isLt)
    simpa [ofIntFin_of_fin] using hf

@[embedding ↓]
theorem forall_fin_out_as_int₃ {n : Nat} {p : (α₁ → α₂ → α₃ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Int,
      (hf : ∀ a₁ a₂ a₃, 0 ≤ f a₁ a₂ a₃ ∧ f a₁ a₂ a₃ < n) →
      p (fun a₁ a₂ a₃ => ofIntFin n (f a₁ a₂ a₃) (hf a₁ a₂ a₃))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ => ofIntFin n (f a₁ a₂ a₃) (hf a₁ a₂ a₃))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => ((f a₁ a₂ a₃ : Nat) : Int)) (fun a₁ a₂ a₃ => by
      constructor
      · exact Int.natCast_nonneg (f a₁ a₂ a₃).val
      · exact Int.ofNat_lt.mpr (f a₁ a₂ a₃).isLt)
    simpa [ofIntFin_of_fin] using hf

@[embedding ↓]
theorem forall_fin_out_as_int₄ {n : Nat} {p : (α₁ → α₂ → α₃ → α₄ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Int,
      (hf : ∀ a₁ a₂ a₃ a₄, 0 ≤ f a₁ a₂ a₃ a₄ ∧ f a₁ a₂ a₃ a₄ < n) →
      p (fun a₁ a₂ a₃ a₄ => ofIntFin n (f a₁ a₂ a₃ a₄) (hf a₁ a₂ a₃ a₄))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ => ofIntFin n (f a₁ a₂ a₃ a₄) (hf a₁ a₂ a₃ a₄))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => ((f a₁ a₂ a₃ a₄ : Nat) : Int)) (fun a₁ a₂ a₃ a₄ => by
      constructor
      · exact Int.natCast_nonneg (f a₁ a₂ a₃ a₄).val
      · exact Int.ofNat_lt.mpr (f a₁ a₂ a₃ a₄).isLt)
    simpa [ofIntFin_of_fin] using hf

@[embedding ↓]
theorem forall_fin_out_as_int₅ {n : Nat} {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Int,
      (hf : ∀ a₁ a₂ a₃ a₄ a₅, 0 ≤ f a₁ a₂ a₃ a₄ a₅ ∧ f a₁ a₂ a₃ a₄ a₅ < n) →
      p (fun a₁ a₂ a₃ a₄ a₅ => ofIntFin n (f a₁ a₂ a₃ a₄ a₅) (hf a₁ a₂ a₃ a₄ a₅))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ a₅ => ofIntFin n (f a₁ a₂ a₃ a₄ a₅) (hf a₁ a₂ a₃ a₄ a₅))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ a₅ => ((f a₁ a₂ a₃ a₄ a₅ : Nat) : Int))
      (fun a₁ a₂ a₃ a₄ a₅ => by
        constructor
        · exact Int.natCast_nonneg (f a₁ a₂ a₃ a₄ a₅).val
        · exact Int.ofNat_lt.mpr (f a₁ a₂ a₃ a₄ a₅).isLt)
    simpa [ofIntFin_of_fin] using hf

@[embedding ↓]
theorem forall_fin_in_as_int₁ {n : Nat} [NeZero n] {p : (Fin n → α₁) → Prop} :
    (∀ f : Fin n → α₁, p f) ↔
    (∀ f : Int → α₁, p (fun a => f ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a => f ((a : Nat) : Int))
  · intro h f
    have hf := h (fun b => f (ofIntFinTotal n b))
    simpa [ofIntFinTotal_of_fin] using hf

@[embedding ↓]
theorem forall_fin_in_as_int₂ {n : Nat} [NeZero n] {p : (α₁ → Fin n → α₂) → Prop} :
    (∀ f : α₁ → Fin n → α₂, p f) ↔
    (∀ f : α₁ → Int → α₂, p (fun a₁ a => f a₁ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a => f a₁ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ b => f a₁ (ofIntFinTotal n b))
    simpa [ofIntFinTotal_of_fin] using hf

@[embedding ↓]
theorem forall_fin_in_as_int₃ {n : Nat} [NeZero n] {p : (α₁ → α₂ → Fin n → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Fin n → α₃, p f) ↔
    (∀ f : α₁ → α₂ → Int → α₃, p (fun a₁ a₂ a => f a₁ a₂ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a => f a₁ a₂ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ b => f a₁ a₂ (ofIntFinTotal n b))
    simpa [ofIntFinTotal_of_fin] using hf

@[embedding ↓]
theorem forall_fin_in_as_int₄ {n : Nat} [NeZero n] {p : (α₁ → α₂ → α₃ → Fin n → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Fin n → α₄, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Int → α₄, p (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ b => f a₁ a₂ a₃ (ofIntFinTotal n b))
    simpa [ofIntFinTotal_of_fin] using hf

@[embedding ↓]
theorem forall_fin_in_as_int₅ {n : Nat} [NeZero n] {p : (α₁ → α₂ → α₃ → α₄ → Fin n → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Fin n → α₅, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Int → α₅,
      p (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ b => f a₁ a₂ a₃ a₄ (ofIntFinTotal n b))
    simpa [ofIntFinTotal_of_fin] using hf

end Smt.Preprocess.Embedding
