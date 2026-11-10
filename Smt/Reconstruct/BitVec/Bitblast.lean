/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean

@[expose] public section

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

private theorem beq_go_iff_window : ∀ {w : Nat} (x y : BitVec w) (i : Nat), i < w →
    (BitVec.beq.go x y i = true ↔
      ∀ j, w - 1 - i ≤ j → j < w → x.getLsbD j = y.getLsbD j) := by
  intro w x y i hi
  induction i with
  | zero =>
    simp only [BitVec.beq.go, beq_iff_eq]
    constructor
    · intro h j hj hj'
      have : j = w - 1 := by omega
      subst this
      exact h
    · intro h
      exact h _ (by omega) (by omega)
  | succ i ih =>
    simp only [BitVec.beq.go, Bool.and_eq_true, beq_iff_eq, ih (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ j hj hj'
      by_cases hc : j = w - 1 - (i + 1)
      · subst hc
        exact h1
      · exact h2 j (by omega) hj'
    · intro h
      exact ⟨h _ (by omega) (by omega), fun j hj hj' ↦ h j (by omega) hj'⟩

private theorem beq_iff_getLsbD : ∀ {w : Nat} (x y : BitVec w),
    (x.beq y = true ↔ ∀ j, j < w → x.getLsbD j = y.getLsbD j) := by
  intro w x y
  cases w with
  | zero => simp [BitVec.beq, BitVec.beq.go]
  | succ n =>
    unfold BitVec.beq
    rw [beq_go_iff_window x y _ (by omega)]
    constructor
    · intro h j hj
      exact h j (by omega) hj
    · intro h j _ hj
      exact h j hj

theorem eq_eq_beq (x : BitVec w) (y : BitVec w) : (x = y) = x.beq y := by
  apply propext
  rw [beq_iff_getLsbD]
  constructor
  · rintro rfl j _
    rfl
  · intro h
    exact BitVec.eq_of_getLsbD_eq (fun j hj ↦ h j hj)

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
