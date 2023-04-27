import Mathlib

infix:30 " ^^ " => xor

namespace Nat

#check Nat.binaryRec
#check bit_val
lemma bit_cases_on (n: Nat) : ∃ n', ∃ b', n = bit b' n' := by
  induction' n using Nat.binaryRec with b n''
  · use 0; use false; simp
  · use n''; use b

lemma bit_0 (b : Bool) : bit b 0 = b.toNat := by
  cases' b <;> simp

example (a b : Nat) (h: a < b ∨ a =b): a≤ b:= by exact le_of_lt_or_eq h


lemma bit_lt (h: bit b n < bit b' m) : n< m ∨ (n=m ∧ b = false ∧ b'= true)   := by 
  cases' b <;> cases' b' <;> simp [bit_val, cond] at *; assumption
  · apply lt_or_eq_of_le; by_contra' h1; linarith
  · by_contra' h1; linarith
  assumption

lemma bit_lt' (h: bit b n < bit b' m) (h1: ¬ (b = false ∧ b'= true)): n < m  := by 
  cases' b <;> cases' b' <;> simp [bit_val, cond] at * <;> linarith

-- MAKE THIS WORK
-- lemma bit_lt (h: bit b n < bit b' m) : cond (b = false ∧ b'= true) (n≤m) (n<m)  := by 
-- cases' b <;> cases' b' <;> simp [bit_val, cond] at * <;> linarith

theorem lt_of_testbit2 (h: n<m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ ∀j, i <j → Nat.testBit m j = Nat.testBit n j := by
  revert m
  induction' n using Nat.binaryRec with b n ih
  <;> intro m
  · intro h
    have ⟨i, hi1, hi2⟩ := exists_most_significant_bit (show m ≠ 0 by linarith)
    use i
    simp [*]; assumption
  · intro h1
    have ⟨m', b', hbn⟩:= bit_cases_on m
    rw [hbn] at h1; rw [hbn]
    cases' bit_lt h1 with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i
      rw [testBit_succ, testBit_succ]
      exact ⟨iH.1, iH.2.1, by 
             intros j hj
             cases' j with j    
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (Order.lt_of_succ_lt_succ hj)]⟩
    · use 0
      simp [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j' , hj⟩ := exists_eq_add_of_le' hj
                                 simp[hj,testBit_succ, h3.1]⟩ 

def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

def bitwise_add (x y z : Nat) : Nat → Nat
  | 0     => z.bit ((x.testBit 0 ^^ y.testBit 0) ^^ bitwise_carry 0 x y)
  | i + 1 =>
    bitwise_add x y (z.bit ((x.testBit (i + 1) ^^ y.testBit (i + 1)) ^^ bitwise_carry x y (i + 1))) i

theorem testBit_add {x y i: Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ bitwise_carry x y i):= by sorry

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y 0 i = (x + y) % 2 ^ (i + 1) := by sorry

def bitwise_not (x y : Nat) : Nat → Nat
  | 0     => y.bit !(x.testBit 0)
  | i + 1 => bitwise_not x (y.bit !(x.testBit (i + 1))) i

def bitwise_not' (x : Nat) : Nat → List Bool
  | 0     => [!(x.testBit 0)]
  | i + 1 => (!x.testBit (i+1)) :: bitwise_not' x i

def bitwise_neg (x i : Nat) : Nat := bitwise_add (bitwise_not x 0 i) 1 0 i

lemma bitwise_not_succ : bitwise_not x y i = bitwise_not x 0 i +2^(i+1)*y := by
  induction' i with i ih generalizing y
  · simp [bitwise_not, bit_val, add_comm]
  · simp only [bitwise_not]
    rw [ih, @ih (bit (!x.testBit (i+1)) 0)]
    simp [bit_val, mul_add,(show 2^(i+1)*(2*y) = 2^(succ (i+1))*y by rw [← mul_assoc]; aesop ), add_assoc, add_comm]
    


lemma testBit_not (h: i ≤ j): (bitwise_not x 0 j).testBit i = !x.testBit i := by
  induction' j with j ih generalizing i
  · simp at h; simp [h, bitwise_not]
  · simp only [bitwise_not]
    rw [bitwise_not_succ]
    sorry

lemma testBit_not' (h: i ≤ j): (toNat.toNat' j (bitwise_not' x j)).testBit i = !x.testBit i := by
  induction' j with j ih generalizing i
  · simp at h; simp [h, bitwise_not', toNat.toNat']; sorry
  · simp only [bitwise_not', toNat.toNat']
    sorry

    

#check Nat.sub_sub
#check testBit_zero

#check tsub_add_eq_add_tsub

example : 1 ≤ 2^i := by exact one_le_pow' i 1
example : 2^(succ i) = 2*2^i := by exact pow_succ'' i 2

example (h: 1 ≤ b)(h2: c ≤ d): c ≤ d*b := by exact le_mul_of_le_of_one_le h2 h

lemma bits_pow_two_minus_one (h: j ≤  i): testBit (2^(i+1) -1) j = true:= by
  induction' i with i ih generalizing j 
  · simp at h; simp [h]
  · have h1: 2^(succ i +1) -1 =  bit true (2^(i+1) -1) := by
      simp only [bit_val, cond]
      rw [Nat.mul_sub_left_distrib, mul_comm, ← pow_succ, mul_one]
      rw [← AddLECancellable.tsub_tsub_assoc (by simp; intros b c hb; linarith) (by rw [pow_succ'']; exact le_mul_of_le_of_one_le (by simp) (one_le_pow' (i+1) 1) ) (by simp)]
    rw[h1]
    cases' j with j j
    · rw[testBit_zero]
    · rw[testBit_succ, ih (le_of_succ_le_succ h)]

theorem bitwise_not_eq_neg_sub_one : 
  bitwise_not x 0 i % 2 ^ (i + 1) + x % 2 ^ (i + 1)  = 2 ^(i + 1) -1 := by 
  apply eq_of_testBit_eq
  intro j
  by_cases h: j ≤ i
  · rw [bits_pow_two_minus_one h, testBit_add]
    



  






theorem bitwise_neg_eq_neg (x i : Nat) :
  bitwise_neg x i % 2 ^ (i + 1) = (2 ^ (i + 1) - x % 2 ^ (i + 1)) % 2 ^ (i + 1) := by
  unfold bitwise_neg
  rw [bitwise_add_eq_add, Nat.add_mod, bitwise_not_eq_neg_sub_one]
  simp
  sorry

#eval bitwise_not 1 0 4
#eval bitwise_neg 4 3

end Nat
