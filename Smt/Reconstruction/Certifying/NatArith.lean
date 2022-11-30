import Lean

open Lean
open Meta
open Elab.Tactic
open Expr

theorem lt_from_lt_le : ∀ {a b c : Nat}, a < b → b ≤ c → a < c := by
  intros a b c h₁ h₂
  have r₁: a + 1 ≤ b := h₁
  have r₂: a + 1 ≤ c := Nat.le_trans r₁ h₂
  exact r₂

theorem lt_from_le_lt : ∀ {a b c : Nat}, a ≤ b → b < c → a < c := by
  intros a b c h₁ h₂
  have r₁: b + 1 ≤ c := h₂
  have r₂: a < b + 1 := Nat.succ_le_succ h₁
  exact lt_from_lt_le r₂ r₁
  
theorem sumBoundsNat₁ : ∀ {a b c d : Nat}, a < b → c < d → a + c < b + d := by
  intros a b c d h₁ h₂
  have r₁ : a + c < a + d := Nat.add_lt_add_left h₂ a
  have r₂ : a + d < b + d := Nat.add_lt_add_right h₁ d
  exact Nat.lt_trans r₁ r₂

theorem sumBoundsNat₂ : ∀ {a b c d : Nat}, a < b → c ≤ d → a + c < b + d := by
  intros a b c d h₁ h₂
  have r₁: a + c ≤ a + d := Nat.add_le_add_left h₂ a
  have r₂: a + d < b + d := Nat.add_lt_add_right h₁ d
  exact lt_from_le_lt r₁ r₂

theorem sumBoundsNat₃ : ∀ {a b c d : Nat}, a < b → c = d → a + c < b + d := by
  intros a b c d h₁ h₂
  rewrite [h₂]
  exact Nat.add_lt_add_right h₁ d

theorem sumBoundsNat₄ : ∀ {a b c d : Nat}, a ≤ b → c < d → a + c < b + d := by
  intros a b c d h₁ h₂
  have r₁ : a + c < a + d := Nat.add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := Nat.add_le_add_right h₁ d
  exact lt_from_lt_le r₁ r₂

theorem sumBoundsNat₅ : ∀ {a b c d : Nat}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  intros a b c d h₁ h₂
  have r₁ : a + c ≤ a + d := Nat.add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := Nat.add_le_add_right h₁ d
  exact Nat.le_trans r₁ r₂

theorem sumBoundsNat₆ : ∀ {a b c d : Nat}, a ≤ b → c = d → a + c ≤ b + d := by
  intros a b c d h₁ h₂
  rewrite [h₂]
  exact Nat.add_le_add_right h₁ d

theorem sumBoundsNat₇ : ∀ {a b c d : Nat}, a = b → c < d → a + c < b + d := by
  intros a b c d h₁ h₂
  rewrite [h₁]
  exact Nat.add_le_add_left h₂ b

theorem sumBoundsNat₈ : ∀ {a b c d : Nat}, a = b → c ≤ d → a + c ≤ b + d := by
  intros a b c d h₁ h₂
  rewrite [h₁]
  exact Nat.add_le_add_left h₂ b

theorem sumBoundsNat₉ : ∀ {a b c d : Nat}, a = b → c = d → a + c ≤ b + d := by
  intros a b c d h₁ h₂
  rewrite [h₁, h₂]
  exact Nat.le_refl (b + d)

syntax (name := sumBounds) "sumBounds" term "," term : tactic

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name :=
      match ← getOp t₁, ← getOp t₂ with
      | `LT.lt , `LT.lt => `sumBoundsNat₁
      | `LT.lt , `LT.le => `sumBoundsNat₂
      | `LT.lt , `Eq    => `sumBoundsNat₃
      | `LE.le , `LT.lt => `sumBoundsNat₄
      | `LE.le , `LE.le => `sumBoundsNat₅
      | `LE.le , `Eq    => `sumBoundsNat₆ 
      | `Eq    , `LT.lt => `sumBoundsNat₇
      | `Eq    , `LE.le => `sumBoundsNat₈
      | `Eq    , `Eq    => `sumBoundsNat₉
      | _      , _      => panic! "[sumBounds] invalid operation"
    closeMainGoal (← mkAppM thmName #[h₁, h₂])
where
  getOp : Expr → TacticM Name
    | app (app (app (app (const nm ..) ..) ..) ..) .. => pure nm
    | app (app (app (const nm ..) ..) ..) .. => pure nm
    | _ => throwError "[sumBounds] invalid parameter"

#check Int.lt


example {a b c d : Nat} : a < b → c = d → a + c < b + d := by
  intros h₁ h₂
  sumBounds h₁, h₂
