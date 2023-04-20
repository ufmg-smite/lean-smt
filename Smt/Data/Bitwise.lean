import Mathlib

infix:30 " ^^ " => xor

namespace Nat

#check Nat.bitCasesOn
lemma bit_cases_on (n: Nat)(h: 2 ≤ n) : ∃ n', ∃ b', n = bit b' n' := by
  sorry


theorem lt_of_testbit2 (h: n<m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ ∀ j<i, Nat.testBit n j = Nat.testBit m j := by
  revert m
  induction' n using Nat.binaryRec with b n ih
  <;> intro m
  · sorry
  · intro h1
    have ⟨m', b', hbn⟩:= bit_cases_on m (by sorry)
    cases' b
    · sorry
    · sorry







def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

def bitwise_add (x y z : Nat) : Nat → Nat
  | 0     => z.bit ((x.testBit 0 ^^ y.testBit 0) ^^ bitwise_carry 0 x y)
  | i + 1 =>
    bitwise_add x y (z.bit ((x.testBit (i + 1) ^^ y.testBit (i + 1)) ^^ bitwise_carry x y (i + 1))) i

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y 0 i = (x + y) % 2 ^ (i + 1) := sorry

def bitwise_not (x y : Nat) : Nat → Nat
  | 0     => y.bit !(x.testBit 0)
  | i + 1 => bitwise_not x (y.bit !(x.testBit (i + 1))) i

def bitwise_neg (x i : Nat) : Nat := bitwise_add (bitwise_not x 0 i) 1 0 i

#eval bitwise_neg 23 4

theorem bitwise_not_eq_neg_sub_one :
  bitwise_not x 0 i % 2 ^ (i + 1) = 2 ^ (i + 1) - 1 - x % 2 ^ (i + 1) := sorry

theorem bitwise_neg_eq_neg (x i : Nat) :
  bitwise_neg x i % 2 ^ (i + 1) = (2 ^ (i + 1) - x % 2 ^ (i + 1)) % 2 ^ (i + 1) := by
  unfold bitwise_neg
  rw [bitwise_add_eq_add, Nat.add_mod, bitwise_not_eq_neg_sub_one]
  simp
  sorry

#eval bitwise_not 0 0 4
#eval bitwise_neg 5 6

end Nat
