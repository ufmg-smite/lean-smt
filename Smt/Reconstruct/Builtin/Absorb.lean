/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

namespace Smt.Reconstruct.Builtin

class Absorb (mul : α → α → α) where
  zero : α
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ (a : α), mul zero a = zero
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ (a : α), mul a zero = zero

instance : Absorb And where
  zero := False
  zero_mul := false_and
  mul_zero := and_false

instance : Absorb Or where
  zero := True
  zero_mul := true_or
  mul_zero := or_true

instance : @Absorb Int (· * ·) where
  zero := 0
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero

instance : @Absorb (BitVec w) (· &&& ·) where
  zero := 0#w
  zero_mul := @BitVec.zero_and w
  mul_zero := @BitVec.and_zero w

instance : @Absorb (BitVec w) (· ||| ·) where
  zero := BitVec.allOnes w
  zero_mul := @BitVec.allOnes_or w
  mul_zero := @BitVec.or_allOnes w

instance : @Absorb (BitVec w) (· * ·) where
  zero := 0#w
  zero_mul := @BitVec.zero_mul w
  mul_zero := @BitVec.mul_zero w

namespace Absorb

def Context α := Nat → α

inductive Expr where
  | zero
  | atom (v : Nat)
  | op (l r : Expr)
deriving Inhabited, Repr

namespace Expr

def containsZero : Expr → Bool
  | Expr.zero   => true
  | Expr.atom _ => false
  | Expr.op l r => containsZero l || containsZero r

def eval [hα : @Absorb α mul] (ctx : Context α) : Expr → α
  | Expr.zero   => hα.zero
  | Expr.atom v => ctx v
  | Expr.op l r => mul (eval (hα := hα) ctx l) (eval (hα := hα) ctx r)

theorem eval_eq_zero_from_containsZero [hα : @Absorb α mul] (ctx : Context α) (h : containsZero e) :
  eval (hα := hα) ctx e = hα.zero := by
  induction e with
  | zero   => rfl
  | atom v => contradiction
  | op l r ih₁ ih₂ =>
    unfold eval
    simp only [containsZero, Bool.or_eq_true] at h
    cases h <;> rename_i h
    · rw [ih₁ h, hα.zero_mul]
    · rw [ih₂ h, hα.mul_zero]

end Expr

end Smt.Reconstruct.Builtin.Absorb
