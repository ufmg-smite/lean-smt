/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Reconstruct.Prop.Core

namespace BitVec

def bb (x : BitVec w) : BitVec w :=
  (iunfoldr (fun i _ => ((), x.getLsb i)) ()).snd

def self_eq_bb (x : BitVec w) : x = x.bb :=
  sorry

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
    | 0     => x.getLsb (w - 1) == y.getLsb (w - 1)
    | i + 1 => x.getLsb ((w - 1) - (i + 1)) == y.getLsb ((w - 1) - (i + 1)) && go i

def eq_eq_beq (x : BitVec w) (y : BitVec w) : (x = y) = x.beq y :=
  sorry

/-- Carry function for bitwise addition. -/
def adcb' (x y c : Bool) : Bool × Bool := (x && y || Bool.xor x y && c, (Bool.xor (Bool.xor x y) c))

theorem adcb_eq_adcb' : adcb = adcb' := by
  funext x y c
  cases x <;> cases y <;> cases c <;> rfl

/-- Bitwise addition implemented via a ripple carry adder. -/
def adc' (x y : BitVec w) : Bool → Bool × BitVec w :=
  iunfoldr fun (i : Fin w) c => adcb' (x.getLsb i) (y.getLsb i) c

theorem adc_eq_adc' : @adc = @adc' := by
  funext x y c
  rw [adc, adc', adcb_eq_adcb']
  rfl

theorem add_eq_adc' (x y : BitVec w) : x + y = (adc' x y false).snd := by
  rw [add_eq_adc, adc_eq_adc']

end BitVec
