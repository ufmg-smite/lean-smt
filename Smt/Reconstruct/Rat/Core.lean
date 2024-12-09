/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Data.Rat

namespace Rat

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

protected theorem add_zero : ∀ a : Rat, a + 0 = a := by
  intro a
  simp only [add_def, zero_den, Int.Nat.cast_ofNat_Int, Int.mul_one, zero_num,
  Int.zero_mul, Int.add_zero, Nat.mul_one]
  exact normalize_self a

open Rat

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d := (divInt_self _).symm

theorem divInt_self' {n : Int} (hn : n ≠ 0) : Rat.divInt n n = 1 := by
  simpa using divInt_mul_right (n := 1) (d := 1) hn

def numDenCasesOn {C : Rat → Sort} :
    ∀ (a : Rat) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (Rat.divInt n d)), C a
  | ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

def numDenCasesOn' {C : Rat → Sort} (a : Rat) (H : ∀ (n : Int) (d : Nat), d ≠ 0 → C (Rat.divInt n d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d (Ne.symm (Nat.ne_of_lt h))

theorem natCast_eq_zero {n : Nat} : (n : Int) = (0 : Int) ↔ n = (0 : Nat) := by omega

theorem add_assoc : ∀ a b c : Rat, a + b + c = a + (b + c) := fun a b c =>
  numDenCasesOn' (C := fun r => r + b + c = r + (b + c)) a fun n₁ d₁ h₁ =>
  numDenCasesOn' (C := fun r => (Rat.divInt n₁ d₁) + r + c = Rat.divInt n₁ d₁ + (r + c)) b fun n₂ d₂ h₂ =>
  numDenCasesOn' (C := fun r => (Rat.divInt n₁ d₁) + (Rat.divInt n₂ d₂) + r = (Rat.divInt n₁ d₁) + ((Rat.divInt n₂ d₂) + r)) c fun n₃ d₃ h₃ => by
    simp only [ne_eq, natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) :=
  numDenCasesOn' (C := fun r => r * b * c = r * (b * c)) a fun n₁ d₁ _ =>
    numDenCasesOn' (C := fun r => (Rat.divInt n₁ d₁) * r * c = (Rat.divInt n₁ d₁) * (r * c)) b fun n₂ d₂ _ =>
      numDenCasesOn' (C := fun r => (Rat.divInt n₁ d₁) * (Rat.divInt n₂ d₂) * r = (Rat.divInt n₁ d₁) * (Rat.divInt n₂ d₂ * r)) c fun n₃ d₃ _ => by
        simp [divInt_ofNat, mkRat_mul_mkRat, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm]


end Rat
