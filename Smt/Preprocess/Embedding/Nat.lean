import Smt.Preprocess.Embedding.Attribute

import Lean

attribute [embedding ↓] Nat.zero_eq
attribute [embedding ↓] Nat.succ_eq_add_one
attribute [embedding ↓] Nat.pred_eq_sub_one
attribute [embedding ↓] Int.toNat_of_nonneg
attribute [embedding ↓] Int.cast_ofNat_Int
attribute [embedding ↓] Int.natCast_add
attribute [embedding ↓] Int.natCast_mul
attribute [embedding ↓] Int.natCast_ediv
attribute [embedding ↓ ←] Int.ofNat_inj
attribute [embedding ↓ ←] Int.ofNat_le
attribute [embedding ↓ ←] Int.ofNat_lt

@[embedding ↓ low]
theorem Int.ofNat_toNat' {x : Int} : x.toNat = if x ≥ 0 then x else 0 := by
  omega

@[embedding ↓]
theorem Int.ite_eq_of_ge_zero {x : Int} (h : x ≥ 0) : (if x ≥ 0 then x else 0) = x :=
  if_pos h

@[embedding ↓]
theorem Int.ofNat_sub' {x y : Nat} : (x - y : Nat) = (if x ≥ y then x - y else 0 : Int) := by
  split <;> rename_i h
  · exact Int.natCast_sub h
  · rewrite [natCast_eq_zero]
    exact Nat.sub_eq_zero_of_le (Nat.le_of_not_le h)

@[embedding ↓ ←]
theorem Int.ofNat_ge {x y : Nat} : ((x : Int) ≥ (y : Int)) ↔ (x ≥ y) := by
  simp only [ge_iff_le, Int.ofNat_le]

@[embedding ↓ ←]
theorem Int.ofNat_gt {x y : Nat} : ((x : Int) > (y : Int)) ↔ (x > y) := by
  simp only [gt_iff_lt, Int.ofNat_lt]

@[embedding ↓ ←]
theorem Int.ofNat_ne {x y : Nat} : ((x : Int) ≠ (y : Int)) ↔ (x ≠ y) := by
  rw [← Decidable.not_iff_not]
  rw [Decidable.not_not, Decidable.not_not]
  rw [Int.ofNat_inj]

@[embedding ↓]
theorem Int.toNat_eq_toNat_of_nonneg {x y : Int} (hx : x ≥ 0) (hy : y ≥ 0) : (x.toNat = y.toNat) ↔ (x = y) := by
  match x, y with
  | .negSucc n, _ => contradiction
  | _, .negSucc m => contradiction
  | .ofNat n, .ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, Int.natCast_inj]

@[embedding ↓]
theorem Int.toNat_ne_toNat_of_nonneg {x y : Int} (hx : x ≥ 0) (hy : y ≥ 0) : (x.toNat ≠ y.toNat) ↔ (x ≠ y) := by
  match x, y with
  | .negSucc n, _ => contradiction
  | _, .negSucc m => contradiction
  | .ofNat n, .ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, ne_eq, Int.natCast_inj]

namespace Smt.Preprocess.Embedding

@[embedding ↓]
theorem forall_nat_as_int {p : Nat → Prop} :
    (∀ f : Nat, p f) ↔ (∀ f : Int, f ≥ 0 → p f.toNat) := by
  constructor
  · intro h f hf
    exact h f.toNat
  · intro h f
    have hf := h (f : Int) (Int.natCast_nonneg f)
    simp only [Int.toNat_natCast] at hf
    exact hf

-- This theorem is similar to the one below, but it does not have the implication in the
-- conclusion of the right-hand side, which (while redundant) helps the simplifier in
-- eliminating `Int.toNat` calls.
theorem exists_nat_as_int {p : Nat → Prop} :
    (∃ x : Nat, p x) ↔ (∃ x : Int, x ≥ 0 ∧ p x.toNat) := by
  constructor
  · intro ⟨x, hx⟩
    exists x
    simp [hx]
  · intro ⟨x, hx₀, hx⟩
    exists x.toNat

@[embedding ↓]
theorem exists_nat_as_int' {p : Nat → Prop} :
    (∃ x : Nat, p x) ↔ (∃ x : Int, x ≥ 0 ∧ (x ≥ 0 → p x.toNat)) := by
  constructor
  · intro ⟨x, hx⟩
    exists x
    simp [hx]
  · intro ⟨x, hx₀, hx⟩
    exists x.toNat
    exact hx hx₀

@[embedding ↓]
theorem forall_nat_out_as_int₁ {p : (α₁ → Nat) → Prop} :
    (∀ f : α₁ → Nat, p f) ↔
    (∀ f : α₁ → Int, (∀ a₁, f a₁ ≥ 0) → p (fun a₁ => (f a₁).toNat)) := by
  constructor
  · intro h f hf
    exact h (fun a₁ => (f a₁).toNat)
  · intro h f
    have hf := h (fun a₁ => (f a₁ : Int)) (fun a₁ => Int.natCast_nonneg (f a₁))
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_out_as_int₂ {p : (α₁ → a₂ → Nat) → Prop} :
    (∀ f : α₁ → a₂ → Nat, p f) ↔
    (∀ f : α₁ → a₂ → Int, (∀ a₁ a₂, f a₁ a₂ ≥ 0) → p (fun a₁ a₂ => (f a₁ a₂).toNat)) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ => (f a₁ a₂).toNat)
  · intro h f
    have hf := h (fun a₁ a₂ => (f a₁ a₂ : Int)) (fun a₁ a₂ => Int.natCast_nonneg (f a₁ a₂))
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_out_as_int₃ {p : (α₁ → a₂ → a₃ → Nat) → Prop} :
    (∀ f : α₁ → a₂ → a₃ → Nat, p f) ↔
    (∀ f : α₁ → a₂ → a₃ → Int, (∀ a₁ a₂ a₃, f a₁ a₂ a₃ ≥ 0) → p (fun a₁ a₂ a₃ => (f a₁ a₂ a₃).toNat)) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ => (f a₁ a₂ a₃).toNat)
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => (f a₁ a₂ a₃ : Int)) (fun a₁ a₂ a₃ => Int.natCast_nonneg (f a₁ a₂ a₃))
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_out_as_int₄ {p : (α₁ → a₂ → a₃ → a₄ → Nat) → Prop} :
    (∀ f : α₁ → a₂ → a₃ → a₄ → Nat, p f) ↔
    (∀ f : α₁ → a₂ → a₃ → a₄ → Int, (∀ a₁ a₂ a₃ a₄, f a₁ a₂ a₃ a₄ ≥ 0) → p (fun a₁ a₂ a₃ a₄ => (f a₁ a₂ a₃ a₄).toNat)) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ => (f a₁ a₂ a₃ a₄).toNat)
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => (f a₁ a₂ a₃ a₄ : Int))
      (fun a₁ a₂ a₃ a₄ => Int.natCast_nonneg (f a₁ a₂ a₃ a₄))
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_out_as_int₅ {p : (α₁ → a₂ → a₃ → a₄ → a₅ → Nat) → Prop} :
    (∀ f : α₁ → a₂ → a₃ → a₄ → a₅ → Nat, p f) ↔
    (∀ f : α₁ → a₂ → a₃ → a₄ → a₅ → Int, (∀ a₁ a₂ a₃ a₄ a₅, f a₁ a₂ a₃ a₄ a₅ ≥ 0) → p (fun a₁ a₂ a₃ a₄ a₅ => (f a₁ a₂ a₃ a₄ a₅).toNat)) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ a₅ => (f a₁ a₂ a₃ a₄ a₅).toNat)
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ a₅ => (f a₁ a₂ a₃ a₄ a₅ : Int))
      (fun a₁ a₂ a₃ a₄ a₅ => Int.natCast_nonneg (f a₁ a₂ a₃ a₄ a₅))
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_in_as_int₁ {p : (Nat → α₁) → Prop} :
    (∀ f : Nat → α₁, p f) ↔
    (∀ f : Int → α₁, p (fun a => f (a : Int))) := by
  constructor
  · intro h f
    exact h (fun a => f (a : Int))
  · intro h f
    have hf := h (fun b => f b.toNat)
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_in_as_int₂ {p : (α₁ → Nat → α₂) → Prop} :
    (∀ f : α₁ → Nat → α₂, p f) ↔
    (∀ f : α₁ → Int → α₂, p (fun a₁ a => f a₁ (a : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a => f a₁ (a : Int))
  · intro h f
    have hf := h (fun a₁ b => f a₁ b.toNat)
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_in_as_int₃ {p : (α₁ → α₂ → Nat → α₃) → Prop} :
  (∀ f : α₁ → α₂ → Nat → α₃, p f) ↔
  (∀ f : α₁ → α₂ → Int → α₃, p (fun a₁ a₂ a => f a₁ a₂ (a : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a => f a₁ a₂ (a : Int))
  · intro h f
    have hf := h (fun a₁ a₂ b => f a₁ a₂ b.toNat)
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_in_as_int₄ {p : (α₁ → α₂ → α₃ → Nat → α₄) → Prop} :
  (∀ f : α₁ → α₂ → α₃ → Nat → α₄, p f) ↔
  (∀ f : α₁ → α₂ → α₃ → Int → α₄, p (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ (a : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ (a : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ b => f a₁ a₂ a₃ b.toNat)
    simp only [Int.toNat_natCast] at hf
    exact hf

@[embedding ↓]
theorem forall_nat_in_as_int₅ {p : (α₁ → α₂ → α₃ → α₄ → Nat → α₅) → Prop} :
  (∀ f : α₁ → α₂ → α₃ → α₄ → Nat → α₅, p f) ↔
  (∀ f : α₁ → α₂ → α₃ → α₄ → Int → α₅, p (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ (a : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ (a : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ b => f a₁ a₂ a₃ a₄ b.toNat)
    simp only [Int.toNat_natCast] at hf
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

private def simpUsingDecide : Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.isTrue || e.isFalse then
    return .continue
  try
    let d ← mkDecide e
    let r ← withDefault <| whnf d
    if r.isConstOf ``true then
      return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
    else if r.isConstOf ``false then
      return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }
    else
      return .continue
  catch _ =>
    return .continue

@[match_pattern]
private abbrev mkIntLitZero :=
  mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int []) (.lit (.natVal 0)) (.app (.const ``instOfNat []) (.lit (.natVal 0)))

def isIntGeLitZero : Expr → Bool
  | .forallE _ _ b _ => isIntGeLitZero b
  | mkApp4 (.const ``LE.le [0]) (.const ``Int []) (.const ``Int.instLEInt []) mkIntLitZero _
  | mkApp4 (.const ``GE.ge [0]) (.const ``Int []) (.const ``Int.instLEInt []) _ mkIntLitZero =>
    true
  | _ => false

def addIntGtZeroLemma : Simproc := fun e => do
  let .forallE _ p q _ := e | return .continue
  if !isIntGeLitZero p then return .continue
  let r ← Meta.withLocalDeclD .anonymous p fun hp => Simp.withFreshCache do
    let qx := q.instantiate1 hp
    let r ← withNewLemmas #[hp] (simp qx)
    r.addForalls #[hp]
  return .continue r

def decideIntGtZero : Simproc := fun e => do
  simpUsingDecide e

simproc ↓ [embedding] add_int_gt_zero (_ → _) :=
  addIntGtZeroLemma

simproc ↓ [embedding] decide_int_gt_zero (_ ≥ (0 : Int)) :=
  Smt.Preprocess.Embedding.decideIntGtZero

end Smt.Preprocess.Embedding
