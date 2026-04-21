/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

namespace BitVec

def bb (x : BitVec w) : BitVec w :=
  (iunfoldr (fun i _ => ((), x.getLsbD i)) ()).snd

theorem self_eq_bb (x : BitVec w) : x = x.bb := by
  unfold bb
  rw [iunfoldr_replace_snd (λ _ => ()) (init:=rfl)]
  intro i
  rfl

-- def beq (x : BitVec w) (y : BitVec w) : Bool :=
--   go w
-- where
--   go : Nat → Bool
--     | 0     => x.getLsb 0 == y.getLsb 0
--     | i + 1 => go i && x.getLsb i == y.getLsb i

-- TODO: fix reconstruction associativity of ∧ to use above version
def beq (x : BitVec w) (y : BitVec w) : Bool :=
  go (w - 1)
where
  go : Nat → Bool
    | 0     => x.getLsbD (w - 1) == y.getLsbD (w - 1)
    | i + 1 => x.getLsbD ((w - 1) - (i + 1)) == y.getLsbD ((w - 1) - (i + 1)) && go i

theorem beq_go_imp_eq {w : Nat} (x y : BitVec w) (i : Nat) :
    beq.go x y i = true → ∀ j, w - 1 - i ≤ j → j < w → x.getLsbD j = y.getLsbD j := by
  induction i with
  | zero =>
    intro h j h1 _
    have hj : j = w - 1 := by omega
    subst hj
    revert h
    unfold beq.go
    intro h
    exact eq_of_beq h
  | succ i ih =>
    intro h j h1 h2
    revert h
    unfold beq.go
    intro h
    have h_and := (Bool.and_eq_true _ _).mp h
    have hj_cases : j = w - 1 - (i + 1) ∨ w - 1 - i ≤ j := by omega
    cases hj_cases with
    | inl hj_eq =>
      subst hj_eq
      exact eq_of_beq h_and.1
    | inr hj_gt =>
      exact ih h_and.2 j hj_gt h2

theorem beq_go_self {w : Nat} (x : BitVec w) (i : Nat) : beq.go x x i = true := by
  induction i with
  | zero =>
    unfold beq.go
    simp
  | succ i ih =>
    unfold beq.go
    simp [ih]

def eq_eq_beq (x : BitVec w) (y : BitVec w) : (x = y) = x.beq y := by
  apply propext
  constructor
  · intro h
    subst h
    unfold beq
    exact beq_go_self x (w - 1)
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold beq at h
    apply beq_go_imp_eq x y (w - 1) h j
    · omega
    · exact hj

/-- Carry function for bitwise addition. -/
def adcb' (x y c : Bool) : Bool × Bool := (x && y || Bool.xor x y && c, (Bool.xor (Bool.xor x y) c))

theorem adcb_eq_adcb' : adcb = adcb' := by
  funext x y c
  cases x <;> cases y <;> cases c <;> rfl

/-- Bitwise addition implemented via a ripple carry adder. -/
def adc' (x y : BitVec w) : Bool → Bool × BitVec w :=
  iunfoldr fun (i : Fin w) c => adcb' (x.getLsbD i) (y.getLsbD i) c

theorem adc_eq_adc' : @adc = @adc' := by
  funext x y c
  rw [adc, adc', adcb_eq_adcb']

theorem add_eq_adc' (x y : BitVec w) : x + y = (adc' x y false).snd := by
  rw [add_eq_adc, adc_eq_adc']

end BitVec
